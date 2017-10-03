{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.PPC.Disassemble ( disassembleFn ) where

import           Control.Lens ( (&), (^.), (%~) )
import           Control.Monad ( unless )
import qualified Control.Monad.Except as ET
import           Control.Monad.ST ( ST )
import           Control.Monad.Trans ( lift )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Foldable as F
import           Data.Proxy ( Proxy(..) )
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import           Data.Word ( Word64 )
import           Text.Printf ( printf )

import qualified Dismantle.PPC as D

import           Data.Macaw.AbsDomain.AbsState as MA
import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import           Data.Macaw.Types ( BVType )
import qualified Data.Parameterized.Nonce as NC

import           Data.Macaw.PPC.Generator
import           Data.Macaw.PPC.PPCReg

-- | Read one instruction from the 'MM.Memory' at the given segmented offset.
--
-- Returns the instruction and number of bytes consumed /or/ an error.
--
-- This code assumes that the 'MM.ByteRegion' is maximal; that is, that there
-- are no byte regions that could be coalesced.
readInstruction :: MM.Memory w
                -> MM.MemSegmentOff w
                -> Either (MM.MemoryError w) (D.Instruction, MM.MemWord w)
readInstruction mem addr = MM.addrWidthClass (MM.memAddrWidth mem) $ do
  let seg = MM.msegSegment addr
  case MM.segmentFlags seg `MMP.hasPerm` MMP.execute of
    False -> ET.throwError (MM.PermissionsError (MM.relativeSegmentAddr addr))
    True -> do
      contents <- MM.addrContentsAfter mem (MM.relativeSegmentAddr addr)
      case contents of
        [] -> ET.throwError (MM.AccessViolation (MM.relativeSegmentAddr addr))
        MM.SymbolicRef {} : _ ->
          ET.throwError (MM.UnexpectedRelocation (MM.relativeSegmentAddr addr))
        MM.ByteRegion bs : _rest
          | BS.null bs -> ET.throwError (MM.AccessViolation (MM.relativeSegmentAddr addr))
          | otherwise -> do
            let (bytesRead, minsn) = D.disassembleInstruction (LBS.fromStrict bs)
            case minsn of
              Just insn -> return (insn, fromIntegral bytesRead)
              Nothing -> ET.throwError (MM.InvalidInstruction (MM.relativeSegmentAddr addr) contents)

disassembleBlock :: forall ppc s
                  . (ArchWidth ppc, ArchReg ppc ~ PPCReg ppc, MM.MemWidth (ArchAddrWidth ppc))
                 => (Value ppc s (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (PPCGenerator ppc s ()))
                 -> MM.Memory (ArchAddrWidth ppc)
                 -> GenState ppc s
                 -> MM.MemSegmentOff (ArchAddrWidth ppc)
                 -> MM.MemWord (ArchAddrWidth ppc)
                 -> DisM ppc s (MM.MemWord (ArchAddrWidth ppc), GenState ppc s)
disassembleBlock lookupSemantics mem gs curIPAddr maxOffset = do
  let seg = MM.msegSegment curIPAddr
  let off = MM.msegOffset curIPAddr
  case readInstruction mem curIPAddr of
    Left err -> failAt gs off curIPAddr (DecodeError err)
    Right (i, bytesRead) -> do
      -- let nextIP = MM.relativeAddr seg (off + bytesRead)
      -- let nextIPVal = MC.RelocatableValue undefined nextIP

      -- Note: In PowerPC, the IP is incremented *after* an instruction
      -- executes, rather than before as in X86.  We have to pass in the
      -- physical address of the instruction here.
      ipVal <- case MM.asAbsoluteAddr (MM.relativeSegmentAddr curIPAddr) of
                 Nothing -> failAt gs off curIPAddr (InstructionAtUnmappedAddr i)
                 Just addr -> return (BVValue (pointerNatRepr (Proxy @ppc)) (fromIntegral addr))
      case lookupSemantics ipVal i of
        Nothing -> failAt gs off curIPAddr (UnsupportedInstruction i)
        Just transformer -> do
          -- FIXME: Do we need to add failure modes here?  Probably.  There are
          -- some invalid encodings that we could encounter that would be worth
          -- failing for.
          egs1 <- liftST $ execGenerator gs $ do
            let line = printf "%s: %s" (show curIPAddr) (show (D.ppInstruction i))
            addStmt (Comment (T.pack  line))
            transformer
          case egs1 of
            Left genErr -> failAt gs off curIPAddr (GenerationError i genErr)
            Right gs1 -> undefined

tryDisassembleBlock :: (ArchWidth ppc, ArchReg ppc ~ PPCReg ppc, MM.MemWidth (ArchAddrWidth ppc))
                    => (Value ppc s (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (PPCGenerator ppc s ()))
                    -> MM.Memory (ArchAddrWidth ppc)
                    -> NC.NonceGenerator (ST s) s
                    -> ArchSegmentOff ppc
                    -> ArchAddrWord ppc
                    -> DisM ppc s ([Block ppc s], MM.MemWord (ArchAddrWidth ppc))
tryDisassembleBlock lookupSemantics mem nonceGen startAddr maxSize = do
  let gs0 = initGenState nonceGen startAddr
  let startOffset = MM.msegOffset startAddr
  (nextIPOffset, gs1) <- disassembleBlock lookupSemantics mem gs0 startAddr (startOffset + maxSize)
  unless (nextIPOffset > startOffset) $ do
    let reason = InvalidNextIP (fromIntegral nextIPOffset) (fromIntegral startOffset)
    failAt gs1 nextIPOffset startAddr reason
  let blocks = F.toList (blockSeq gs1 ^. frontierBlocks)
  return (blocks, nextIPOffset - startOffset)

-- | Disassemble a block from the given start address (which points into the
-- 'MM.Memory').
--
-- Return a list of disassembled blocks as well as the total number of bytes
-- occupied by those blocks.
disassembleFn :: (ArchWidth ppc, ArchReg ppc ~ PPCReg ppc, MM.MemWidth (RegAddrWidth (ArchReg ppc)))
              => proxy ppc
              -> (Value ppc s (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (PPCGenerator ppc s ()))
              -- ^ A function to look up the semantics for an instruction.  The
              -- lookup is provided with the value of the IP in case IP-relative
              -- addressing is necessary.
              -> MM.Memory (ArchAddrWidth ppc)
              -- ^ The mapped memory space
              -> NC.NonceGenerator (ST s) s
              -- ^ A generator of unique IDs used for assignments
              -> ArchSegmentOff ppc
              -- ^ The address to disassemble from
              -> ArchAddrWord ppc
              -- ^ Maximum size of the block (a safeguard)
              -> MA.AbsBlockState (ArchReg ppc)
              -- ^ Abstract state of the processor at the start of the block
              -> ST s ([Block ppc s], MM.MemWord (ArchAddrWidth ppc), Maybe String)
disassembleFn _ lookupSemantics mem nonceGen startAddr maxSize _  = do
  mr <- ET.runExceptT (unDisM (tryDisassembleBlock lookupSemantics mem nonceGen startAddr maxSize))
  case mr of
    Left (blocks, off, exn) -> return (blocks, off, Just (show exn))
    Right (blocks, bytes) -> return (blocks, bytes, Nothing)

finishBlock' :: PreBlock ppc s
             -> (RegState (PPCReg ppc) (Value ppc s) -> TermStmt ppc s)
             -> Block ppc s
finishBlock' preBlock term =
  Block { blockLabel = pBlockIndex preBlock
        , blockAddr = pBlockAddr preBlock
        , blockStmts = F.toList (preBlock ^. pBlockStmts)
        , blockTerm = term (preBlock ^. pBlockState)
        }

finishBlock :: (RegState (PPCReg ppc) (Value ppc s) -> TermStmt ppc s)
            -> GenResult ppc s
            -> BlockSeq ppc s
finishBlock term st =
  case resState st of
    Nothing -> resBlockSeq st
    Just preBlock ->
      let b = finishBlock' preBlock term
      in resBlockSeq st & frontierBlocks %~ (Seq.|> b)

type LocatedError ppc s = ([Block ppc s], MM.MemWord (ArchAddrWidth ppc), TranslationError (ArchAddrWidth ppc))
newtype DisM ppc s a = DisM { unDisM :: ET.ExceptT (LocatedError ppc s) (ST s) a }
  deriving (Functor,
            Applicative,
            Monad)

-- | This funny instance is required because GHC doesn't allow type function
-- applications in instance heads, so we factor the type functions out into a
-- constraint on a fresh variable.  See
--
-- > https://stackoverflow.com/questions/45360959/illegal-type-synonym-family-application-in-instance-with-functional-dependency
--
-- We also can't derive this instance because of that restriction (but deriving
-- silently fails).
instance (w ~ ArchAddrWidth ppc) => ET.MonadError ([Block ppc s], MM.MemWord w, TranslationError w) (DisM ppc s) where
  throwError e = DisM (ET.throwError e)

data TranslationError w = TranslationError { transErrorAddr :: MM.MemSegmentOff w
                                           , transErrorReason :: TranslationErrorReason w
                                           }

data TranslationErrorReason w = InvalidNextIP Word64 Word64
                              | DecodeError (MM.MemoryError w)
                              | UnsupportedInstruction D.Instruction
                              | InstructionAtUnmappedAddr D.Instruction
                              | GenerationError D.Instruction GeneratorError
                              deriving (Show)

deriving instance (MM.MemWidth w) => Show (TranslationError w)

liftST :: ST s a -> DisM ppc s a
liftST = DisM . lift

failAt :: forall ppc s a
        . (ArchReg ppc ~ PPCReg ppc, MM.MemWidth (ArchAddrWidth ppc))
       => GenState ppc s
       -> MM.MemWord (ArchAddrWidth ppc)
       -> MM.MemSegmentOff (ArchAddrWidth ppc)
       -> TranslationErrorReason (ArchAddrWidth ppc)
       -> DisM ppc s a
failAt gs offset curIPAddr reason = do
  let exn = TranslationError { transErrorAddr = curIPAddr
                             , transErrorReason = reason
                             }
  let term = (`TranslateError` T.pack (show exn))
  let b = finishBlock' (gs ^. blockState) term
  let res = blockSeq gs & frontierBlocks %~ (Seq.|> b)
  let res' = F.toList (res ^. frontierBlocks)
  ET.throwError (res', offset, exn)
