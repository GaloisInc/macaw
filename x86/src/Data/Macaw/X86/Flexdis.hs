{-
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This provides a facility for disassembling x86 instructions from a
Macaw memory objec.t
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.X86.Flexdis
  ( MemoryByteReader
  , runMemoryByteReader
  , readInstruction
  ) where

import           Control.Monad.Except
import           Control.Monad.State.Strict
import qualified Data.ByteString as BS
import           Data.Word

import           Data.Macaw.Memory
import qualified Data.Macaw.Memory.Permissions as Perm

import qualified Flexdis86 as Flexdis
import           Flexdis86.ByteReader

------------------------------------------------------------------------
-- MemStream

data PrevData w = PrevData { prevBytes :: [Word8]
                           , prevRanges :: [SegmentRange w]
                           }

emptyPrevData :: PrevData w
emptyPrevData = PrevData { prevBytes = [], prevRanges = [] }

consByte :: Word8 -> PrevData w -> PrevData w
consByte w pd = pd { prevBytes = w:prevBytes pd
                   }

prevSegments :: PrevData w -> [SegmentRange w]
prevSegments pd | null (prevBytes pd) = reverse (prevRanges pd)
                | otherwise = reverse (prevRanges pd) ++ [ByteRegion (BS.pack (prevBytes pd))]

-- | A stream of memory
data MemStream w = MS { msSegment :: !(MemSegment w)
                        -- ^ The current segment
                      , msStart :: !(MemWord w)
                        -- ^ The initial offset for the stream.
                      , msPrev :: !(PrevData w)
                        -- ^ The values read so far.
                      , msOffset :: !(MemWord w)
                        -- ^ The current address
                      , msNext :: ![SegmentRange w]
                        -- ^ The next bytes to read.
                      }

msStartAddr :: MemWidth w => MemStream w -> MemAddr w
msStartAddr ms = relativeSegmentAddr segOff
  where Just segOff = resolveSegmentOff (msSegment ms) (msStart ms)

msAddr :: MemWidth w => MemStream w -> MemAddr w
msAddr ms = relativeSegmentAddr segOff
  where Just segOff = resolveSegmentOff (msSegment ms) (msOffset ms)

------------------------------------------------------------------------
-- MemoryByteReader

newtype MemoryByteReader w a = MBR { unMBR :: ExceptT (MemoryError w) (State (MemStream w)) a }
  deriving (Functor, Applicative, MonadError (MemoryError w))

instance MemWidth w => Monad (MemoryByteReader w) where
  return = MBR . return
  MBR m >>= f = MBR $ m >>= unMBR . f
  fail msg = do
    addr <- MBR $ gets msAddr
    throwError $ UserMemoryError addr msg

-- | Create a memory stream pointing to given address, and return pair whose
-- first element is the value read or an error, and whose second element is
-- the address of the next value to read.
runMemoryByteReader :: Memory w
                    -> Perm.Flags
                       -- ^ Permissions that memory accesses are expected to
                       -- satisfy.
                       -- Added so we can check for read and/or execute permission.
                    -> MemSegmentOff w -- ^ Starting segment
                    -> MemoryByteReader w a -- ^ Byte reader to read values from.
                    -> Either (MemoryError w) (a, MemWord w)
runMemoryByteReader mem reqPerm addr (MBR m) = do
  addrWidthClass (memAddrWidth mem) $ do
  let seg = msegSegment addr
  if not (segmentFlags seg `Perm.hasPerm` reqPerm) then
    Left $ PermissionsError (relativeSegmentAddr addr)
   else do
    contents <- addrContentsAfter mem (relativeSegmentAddr addr)
    let ms0 = MS { msSegment = seg
                 , msStart   = msegOffset addr
                 , msPrev    = emptyPrevData
                 , msOffset  = msegOffset addr
                 , msNext    = contents
                 }
    case runState (runExceptT m) ms0 of
      (Left e, _) -> Left e
      (Right v, ms) -> Right (v, msOffset ms)

instance MemWidth w => ByteReader (MemoryByteReader w) where
  readByte = do
    ms <- MBR get
    -- If remaining bytes are empty
    case msNext ms of
      [] ->
        MBR $ throwError $ AccessViolation (msAddr ms)
      -- Throw error if we try to read a relocation as a symbolic reference
      SymbolicRef{}:_ -> do
        MBR $ throwError $ UnexpectedRelocation (msAddr ms)
      ByteRegion bs:rest -> do
        if BS.null bs then do
          throwError $ AccessViolation (msAddr ms)
         else do
          let v = BS.head bs
          let ms' = ms { msPrev   = consByte v (msPrev ms)
                       , msOffset = msOffset ms + 1
                       , msNext   = ByteRegion (BS.tail bs) : rest
                       }
          MBR $ v <$ put ms'
  invalidInstruction = do
    ms <- MBR $ get
    throwError $ InvalidInstruction (msStartAddr ms) (prevSegments (msPrev ms))

------------------------------------------------------------------------
-- readInstruction

-- | Read instruction at a given memory address.
readInstruction :: Memory 64
                -> MemSegmentOff 64
                   -- ^ Address to read from.
                -> Either (MemoryError 64)
                          (Flexdis.InstructionInstance, MemWord 64)
readInstruction mem addr = runMemoryByteReader mem Perm.execute addr m
  where m = Flexdis.disassembleInstruction
