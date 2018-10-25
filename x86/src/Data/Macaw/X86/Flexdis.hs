{-
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This provides a facility for disassembling x86 instructions from a
Macaw memory object.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.X86.Flexdis
  ( readInstruction
  , InstructionDecodeError(..)
  , RelocPos(..)
  ) where

import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Data.Bits
import qualified Data.ByteString as BS
import           Data.Int
import           Data.Word

import           Data.Macaw.Memory

import qualified Flexdis86 as Flexdis
import           Flexdis86.ByteReader

------------------------------------------------------------------------
-- MemStream

-- | A stream of memory
data MemStream w = MS { msInitial :: ![MemChunk w]
                        -- ^ Initial memory contents.  Used for error messages.
                      , msOffset :: !(MemWord w)
                        -- ^ Offset of msState
                      , msNext :: ![MemChunk w]
                        -- ^ The next bytes to read.
                      }

------------------------------------------------------------------------
-- MemoryByteReader

-- | Descriptor of which function encountered a relocation.
data RelocPos
   = ReadByte
   | ReadJump
   | ReadImm32

-- | Errors thrown when decoding an instruction.
data InstructionDecodeError w
   = UserDecodeError !String
     -- ^ the memory reader threw an unspecified error at the given offset.
   | EndOfInstruction
     -- ^ Unexpected end of instruction.
   | UnsupportedRelocation !RelocPos !(Relocation w)
     -- ^ A relocation appeared in given position.
   | BSSEncountered
     -- ^ We encountered BSS data when decoding instruction.s
   | InvalidInstruction ![SegmentRange w]
     -- ^ We could not decode the instruction.

instance Show (InstructionDecodeError w) where
  show err =
    case err of
      UserDecodeError msg ->
        msg
      EndOfInstruction ->
        "Unexpected end of instruction."
      UnsupportedRelocation loc r ->
        let sloc = case loc of
                     ReadByte -> "byte"
                     ReadImm32 -> "32-bit immediate"
                     ReadJump -> "jump"
        in "Unexpected relocation when decoding " ++ sloc ++ ":\n"
           ++ "  " ++ show r
      BSSEncountered ->
        "Do not support decoding instructions within .bss."
      InvalidInstruction rng ->
        "Could not decode instruction " ++ show rng


newtype MemoryByteReader w a = MBR { unMBR :: ExceptT (MemWord w, InstructionDecodeError w) (State (MemStream w)) a }
  deriving (Functor, Applicative, MonadError (MemWord w, InstructionDecodeError w))

throwDecodeError :: MemWidth w => InstructionDecodeError w -> MemoryByteReader w a
throwDecodeError e = do
  off <- MBR $ gets msOffset
  throwError $! (off, e)

instance MemWidth w => Monad (MemoryByteReader w) where
  return = MBR . return
  MBR m >>= f = MBR $ m >>= unMBR . f
  fail msg = throwDecodeError $ UserDecodeError msg

-- | Run a memory byte reader starting from the given offset.
--
-- This returns either the translate error or the value read, the offset read to, and
-- the next data.
runMemoryByteReader :: MemWidth w
                    => [MemChunk w] -- ^ Data to read next.
                    -> MemoryByteReader w a -- ^ Byte reader to read values from.
                    -> Either (Int, InstructionDecodeError w) (a, Int, [MemChunk w])
runMemoryByteReader contents (MBR m) = do
  let ms0 = MS { msInitial = contents
               , msOffset  = 0
               , msNext    = contents
               }
  case runState (runExceptT m) ms0 of
    (Left (off, e), _) -> Left (fromIntegral off, e)
    (Right v, ms) -> Right (v, fromIntegral (msOffset ms), msNext ms)

sbyte :: (Bits w, Num w) => Word8 -> Int -> w
sbyte w o = fromIntegral i8 `shiftL` (8*o)
  where i8 :: Int8
        i8 = fromIntegral w

ubyte :: (Bits w, Num w) => Word8 -> Int -> w
ubyte w o = fromIntegral w `shiftL` (8*o)

jsizeCount :: Flexdis.JumpSize -> Int
jsizeCount Flexdis.JSize8  = 1
jsizeCount Flexdis.JSize16 = 2
jsizeCount Flexdis.JSize32 = 4

getUnsigned32 :: MemWidth w => BS.ByteString -> MemoryByteReader w Word32
getUnsigned32 s =
  case BS.unpack s of
    w0:w1:w2:w3:_ -> do
      pure $! ubyte w3 3 .|. ubyte w2 2 .|. ubyte w1 1 .|. ubyte w0 0
    _ -> do
      throwDecodeError $ EndOfInstruction

getJumpBytes :: MemWidth w => BS.ByteString -> Flexdis.JumpSize -> MemoryByteReader w (Int64, Int)
getJumpBytes s sz =
  case (sz, BS.unpack s) of
    (Flexdis.JSize8, w0:_) -> do
      pure (sbyte w0 0, 1)
    (Flexdis.JSize16, w0:w1:_) -> do
      pure (sbyte w1 1 .|. ubyte w0 0, 2)
    (Flexdis.JSize32, _) -> do
      v <- getUnsigned32 s
      pure (fromIntegral (fromIntegral v :: Int32), 4)
    _ -> do
      throwDecodeError $ EndOfInstruction

updateMSByteString :: MemWidth w
                   => MemStream w
                   -> BS.ByteString
                   -> [MemChunk w]
                   -> MemWord w
                   -> MemoryByteReader w ()
updateMSByteString ms bs rest c = do
  let bs' = BS.drop (fromIntegral (memWordToUnsigned c)) bs
  let ms' = ms { msOffset = msOffset ms + c
               , msNext   =
                 if BS.null bs' then
                   rest
                  else
                   ByteRegion bs' : rest
               }
  seq ms' $ MBR $ put ms'


instance MemWidth w => ByteReader (MemoryByteReader w) where
  readByte = do
    ms <- MBR get
    -- If remaining bytes are empty
    case msNext ms of
      [] ->
        throwDecodeError $ EndOfInstruction
      -- Throw error if we try to read a relocation as a symbolic reference
      BSSRegion _:_ -> do
        throwDecodeError $ BSSEncountered
      RelocationRegion r:_ ->
        throwDecodeError $ UnsupportedRelocation ReadByte r
      ByteRegion bs:rest -> do
        if BS.null bs then do
          throwDecodeError $ EndOfInstruction
         else do
          let v = BS.head bs
          updateMSByteString ms bs rest 1
          pure $! v

  readDImm = do
    ms <- MBR get
    -- If remaining bytes are empty
    case msNext ms of
      [] ->
        throwDecodeError $ EndOfInstruction
      -- Throw error if we try to read a relocation as a symbolic reference
      BSSRegion _:_ -> do
        throwDecodeError $ BSSEncountered
      RelocationRegion r:rest -> do
        let sym = relocationSym r
        let off = relocationOffset r
        let isGood
              =  relocationIsRel r == False
              && relocationSize r == 4
              && relocationEndianness r == LittleEndian
        when (not isGood) $ do
          throwDecodeError $ UnsupportedRelocation ReadImm32 r
        -- Returns whether the bytes in this relocation are thought of as signed or unsigned.
        let signed = relocationIsSigned r

        let ms' = ms { msOffset = msOffset ms + 4
                     , msNext   = rest
                     }
        seq ms' $ MBR $ put ms'
        pure $ Flexdis.Imm32SymbolOffset sym (fromIntegral off) signed

      ByteRegion bs:rest -> do
        v <- getUnsigned32 bs
        updateMSByteString ms bs rest 4
        pure $! Flexdis.Imm32Concrete (fromIntegral v)

  readJump sz = do
    ms <- MBR get
    -- If remaining bytes are empty
    case msNext ms of
      [] ->
        throwDecodeError $ EndOfInstruction
      -- Throw error if we try to read a relocation as a symbolic reference
      BSSRegion _:_ -> do
        throwDecodeError $ BSSEncountered
      RelocationRegion r:rest -> do
        let sym = relocationSym r
        let off = relocationOffset r
        -- Sanity checks
        let isGood
              =  relocationIsRel r
              && relocationSize r == jsizeCount sz
              && relocationIsSigned r == False
              && relocationEndianness r == LittleEndian
        when (not isGood) $ do
          throwDecodeError $ UnsupportedRelocation ReadJump r
        let ms' = ms { msOffset = msOffset ms + fromIntegral (jsizeCount sz)
                     , msNext   = rest
                     }
        seq ms' $ MBR $ put ms'
        let ioff = fromIntegral $ msOffset ms
        pure $ Flexdis.RelativeOffset ioff sym (fromIntegral off)
      ByteRegion bs:rest -> do
        (v,c) <- getJumpBytes bs sz
        updateMSByteString ms bs rest (fromIntegral c)
        pure (Flexdis.FixedOffset v)

  invalidInstruction = do
    ms <- MBR $ get
    let e = InvalidInstruction $ takeSegmentPrefix (msInitial ms) (msOffset ms)
    throwError (0, e)

------------------------------------------------------------------------
-- readInstruction

-- | Read instruction with given contents.
readInstruction :: [MemChunk 64] -- ^ Data to read next.
                -> Either (Int, InstructionDecodeError 64)
                          (Flexdis.InstructionInstance
                          , Int
                          , [MemChunk 64]
                          )
readInstruction contents =
  runMemoryByteReader contents Flexdis.disassembleInstruction
