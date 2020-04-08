{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-

General notes regarding the disassembly process for ARM.

ARM disassembly is complicated by the different instruction set states
that an ARM processor supports.  There are technically 4 different
instruction sets: ARM32, Thumb32, Thumb32EE, and Jazelle.  At the
present time, only the first two are supported by macaw-arm
(identified hereafter as A32 and T32).

When macaw base's Discovery is attempting to discover code to
construct the CFG and attach it to the semantics, it is unaware of
these different instruction set modes.

Normally a switch from one instruction set to another is accomplished
via a cross-mode branch (e.g. BRX), which will be identified by normal
processes as the end of a particular code block.  However, there are
many instructions which can target R15 (i.e. the PC) and therefore
potentially cause an ISETSTATE (Instruction Set State) switch.

To handle the above:

  * At the beginning of disassembly, a current mode must be known.
    Although macaw-base could be extended to allow the
    architecture-specific module to persist information across calls
    to disassembly, this value can also be extracted from the initial
    AbsProcessorState.

  * The disassembly should only try to disassemble for the current
    mode, and should exit (with the FetchAndExecute status) whenever
    the ISETSTATE changes. (This may require enhancing the
    post-semantics disassembleBlock functionality below to detect
    ISETSTATE differences).

  * The macaw-base functionality will then create a block up to this
    point, and the FetchAndExecute status will cause the instructions
    at this point to be declared as another frontier for subsequent
    block discovery.  The AbsProcessorState associated with this
    frontier will inform the subsequent call to disassemblyFn which
    ISETSTATE is applicable for that disassembly.

Notes:

  * At the present time (Aug 15 2018), the code below *improperly*
    attempts to use the low bit of the PC register to determine which
    operational mode is newly in effect.  This is wrong because the
    semantics for an instruction will effect the ISETSTATE change and
    then clear the bits when writing to the PC.  This should be
    re-worked to use the above described functionality instead.
-}

module Data.Macaw.ARM.Disassemble
    ( disassembleFn
    )
    where

import           Control.Lens ( (^.), (.~) )
import           Control.Monad ( unless )
import qualified Control.Monad.Except as ET
import           Control.Monad.ST ( ST )
import           Control.Monad.Trans ( lift )
import           Data.Bits
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import           Data.Macaw.ARM.ARMReg
import           Data.Macaw.ARM.Arch()
import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import           Data.Macaw.SemMC.Generator
import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Macaw.Types
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as NC
import qualified Data.Text as T
import qualified Dismantle.ARM.A32 as ARMD
import qualified Dismantle.ARM.T32 as ThumbD
import           Text.Printf ( printf )

import qualified SemMC.Architecture.AArch32 as ARM
-- We need this for an orphan instance
import           Data.Macaw.ARM.Simplify ()

data InstructionSet = A32I ARMD.Instruction | T32I ThumbD.Instruction
                      deriving (Eq, Show)


-- | Disassemble a block from the given start address (which points into the
-- 'MM.Memory').
--
-- Return a list of disassembled blocks as well as the total number of bytes
-- occupied by those blocks.
disassembleFn :: proxy ARM.AArch32
              -> (Value ARM.AArch32 ids (BVType (ArchAddrWidth ARM.AArch32)) -> ARMD.Instruction -> Maybe (Generator ARM.AArch32 ids s ()))
              -- ^ A function to look up the semantics for an A32 instruction.  The
              -- lookup is provided with the value of the IP in case IP-relative
              -- addressing is necessary.
              -> (Value ARM.AArch32 ids (BVType (ArchAddrWidth ARM.AArch32)) -> ThumbD.Instruction -> Maybe (Generator ARM.AArch32 ids s ()))
              -- ^ A function to look up the semantics for a T32 instruction.  The
              -- lookup is provided with the value of the IP in case IP-relative
              -- addressing is necessary.
              -> NC.NonceGenerator (ST s) ids
              -- ^ A generator of unique IDs used for assignments
              -> ArchSegmentOff ARM.AArch32
              -- ^ The address to disassemble from
              -> (RegState (ArchReg ARM.AArch32) (Value ARM.AArch32 ids))
              -- ^ The initial registers
              -> Int
              -- ^ Maximum size of the block (a safeguard)
              -> ST s (Block ARM.AArch32 ids, Int)
disassembleFn _ lookupA32Semantics lookupT32Semantics nonceGen startAddr regState maxSize = do
  let lookupSemantics ipval instr = case instr of
                                      A32I inst -> lookupA32Semantics ipval inst
                                      T32I inst -> lookupT32Semantics ipval inst
  mr <- ET.runExceptT (unDisM (tryDisassembleBlock
                               lookupSemantics
                               nonceGen startAddr regState maxSize))
  case mr of
    Left (blocks, off, _exn) -> return (blocks, off)
    Right (blocks, bytes) -> return (blocks, bytes)

tryDisassembleBlock :: (Value ARM.AArch32 ids (BVType (ArchAddrWidth ARM.AArch32)) -> InstructionSet -> Maybe (Generator ARM.AArch32 ids s ()))
                    -> NC.NonceGenerator (ST s) ids
                    -> ArchSegmentOff ARM.AArch32
                    -> RegState (ArchReg ARM.AArch32) (Value ARM.AArch32 ids)
                    -> Int
                    -> DisM ARM.AArch32 ids s (Block ARM.AArch32 ids, Int)
tryDisassembleBlock lookupSemantics nonceGen startAddr regState maxSize = do
  let gs0 = initGenState nonceGen startAddr regState
  let startOffset = MM.segoffOffset startAddr
  (nextPCOffset, block) <- disassembleBlock lookupSemantics gs0 startAddr 0 (startOffset + fromIntegral maxSize)
  unless (nextPCOffset > startOffset) $ do
    let reason = InvalidNextPC (MM.absoluteAddr nextPCOffset) (MM.absoluteAddr startOffset)
    failAt gs0 nextPCOffset startAddr reason
  return (block, fromIntegral (nextPCOffset - startOffset))



-- | Disassemble an instruction and terminate the current block if we run out of
-- instructions to disassemble.  We can run out if:
--
-- 1) We exceed the offset that macaw has told us to disassemble to
--
-- 2) We can't decode the IP (i.e., it isn't a constant)
--
-- 3) The IP after executing the semantics transformer is not equal to the
--    expected next IP value, which indicates a jump to another block or
--    function
--
-- In most of those cases, we end the block with a simple terminator.  If the IP
-- becomes a mux, we split execution using 'conditionalBranch'.
disassembleBlock :: forall ids s .
                    (Value ARM.AArch32 ids (BVType 32) -> InstructionSet -> Maybe (Generator ARM.AArch32 ids s ()))
                 -- ^ A function to look up the semantics for an instruction that we disassemble
                 -> GenState ARM.AArch32 ids s
                 -> MM.MemSegmentOff 32
                 -- ^ The current instruction pointer
                 -> MM.MemWord 32
                 -- ^ The offset into the block of this instruction
                 -> MM.MemWord 32
                 -- ^ The maximum offset into the bytestring that we should
                 -- disassemble to; in principle, macaw can tell us to limit our
                 -- search with this.
                 -> DisM ARM.AArch32 ids s (MM.MemWord 32, Block ARM.AArch32 ids)
disassembleBlock lookupSemantics gs curPCAddr blockOff maxOffset = do
  let seg = MM.segoffSegment curPCAddr
  let off = MM.segoffOffset curPCAddr
  case readInstruction curPCAddr of
    Left err -> failAt gs off curPCAddr (DecodeError err)
    Right (_, 0) -> failAt gs off curPCAddr (InvalidNextPC (MM.segoffAddr curPCAddr) (MM.segoffAddr curPCAddr))
    Right (i, bytesRead) -> do
      -- FIXME: Set PSTATE.T based on whether instruction is A32I or T32I
      -- traceM ("II: " ++ show i)
      -- let curPC = MM.segmentOffAddr seg off
      let nextPCOffset = off + bytesRead
          nextPC = MM.segmentOffAddr seg nextPCOffset
          nextPCVal :: Value ARM.AArch32 ids (BVType 32) = MC.RelocatableValue (MM.addrWidthRepr curPCAddr) nextPC
          -- curPCVal :: Value ARM.AArch32 ids (BVType 32) = MC.RelocatableValue (MM.addrWidthRepr curPCAddr) curPC
      -- Note: In ARM, the IP is incremented *after* an instruction
      -- executes; pass in the physical address of the instruction here.
      ipVal <- case MM.asAbsoluteAddr (MM.segoffAddr curPCAddr) of
                 Nothing -> failAt gs off curPCAddr (InstructionAtUnmappedAddr i)
                 Just addr -> return (BVValue (knownNat :: NatRepr 32) (fromIntegral addr))
      case lookupSemantics ipVal i of
        Nothing -> failAt gs off curPCAddr (UnsupportedInstruction i)
        Just transformer -> do
          -- Once we have the semantics for the instruction (represented by a
          -- state transformer), we apply the state transformer and then extract
          -- a result from the state of the 'Generator'.
          egs1 <- liftST $ ET.runExceptT (runGenerator unfinishedBlock gs $ do
            let lineStr = printf "%s: %s" (show curPCAddr) (show (case i of
                                                                    A32I i' -> ARMD.ppInstruction i'
                                                                    T32I i' -> ThumbD.ppInstruction i'))
            addStmt (InstructionStart blockOff (T.pack lineStr))
            addStmt (Comment (T.pack  lineStr))
            setRegVal branchTaken (CValue (BoolCValue False))
            asAtomicStateUpdate (MM.segoffAddr curPCAddr) transformer)
          case egs1 of
            Left genErr -> failAt gs off curPCAddr (GenerationError i genErr)
            Right gs1 -> do
              case gs1 of
                UnfinishedPartialBlock preBlock ->
                  if | CValue (BoolCValue False) <- preBlock ^. (pBlockState . boundValue branchTakenReg)
                     , Just nextPCSegAddr <- MM.incSegmentOff curPCAddr (fromIntegral bytesRead) -> do
                    -- If the branch taken flag is anything besides a
                    -- concrete False value, then we are at the end of a
                    -- block.
                      let preBlock' = (pBlockState . curIP .~ nextPCVal) preBlock
                      let gs2 = GenState { assignIdGen = assignIdGen gs
                                         , _blockState = preBlock'
                                         , genAddr = nextPCSegAddr
                                         , genRegUpdates = MapF.empty
                                         }
                      disassembleBlock lookupSemantics gs2 nextPCSegAddr (blockOff + fromIntegral bytesRead) maxOffset
                     -- Otherwise, we are still at the end of a block.
                     | otherwise -> return (nextPCOffset, finishBlock' preBlock FetchAndExecute)
                FinishedPartialBlock b -> return (nextPCOffset, b)

-- | Read one instruction from the 'MM.Memory' at the given segmented offset.
--
-- Returns the instruction and number of bytes consumed /or/ an error.
--
-- This code assumes that the 'MM.ByteRegion' is maximal; that is, that there
-- are no byte regions that could be coalesced.
readInstruction :: (MM.MemWidth w)
                => MM.MemSegmentOff w
                -> Either (ARMMemoryError w) (InstructionSet, MM.MemWord w)
readInstruction addr = do
  let seg = MM.segoffSegment addr
  let segRelAddr = MM.segoffAddr addr
  -- Addresses specified in ARM instructions have the low bit
  -- clear, but Thumb (T32) target addresses have the low bit sit.
  -- This is only manifested in the instruction addresses: the
  -- actual PC for fetching instructions clears the low bit to
  -- generate aligned memory accesses.
  let alignedMsegOff = MM.clearSegmentOffLeastBit addr
  if MM.segmentFlags seg `MMP.hasPerm` MMP.execute
  then do
      -- traceM ("Orig addr = " ++ show addr ++ " modified to " ++ show ao)
      -- alignedMsegOff <- liftMaybe (ARMInvalidInstructionAddress seg ao) (MM.resolveSegmentOff seg ao)
      contents <- liftMemError $ MM.segoffContentsAfter alignedMsegOff
      case contents of
        [] -> ET.throwError $ ARMMemoryError (MM.AccessViolation segRelAddr)
        MM.BSSRegion {} : _ ->
          ET.throwError $ ARMMemoryError (MM.UnexpectedBSS segRelAddr)
        MM.RelocationRegion r : _ ->
          ET.throwError $ ARMMemoryError (MM.UnexpectedRelocation segRelAddr r)
        MM.ByteRegion bs : _
          | BS.null bs -> ET.throwError $ ARMMemoryError (MM.AccessViolation segRelAddr)
          | otherwise -> do
            -- FIXME: Having to wrap the bytestring in a lazy wrapper is
            -- unpleasant.  We could alter the disassembler to consume strict
            -- bytestrings, at the cost of possibly making it less efficient for
            -- other clients.
            let (bytesRead, minsn) =
                         if segoffOffset addr .&. 1 == 0
                         then fmap (fmap A32I) $ ARMD.disassembleInstruction (LBS.fromStrict bs)
                         else fmap (fmap T32I) $ ThumbD.disassembleInstruction (LBS.fromStrict bs)
            case minsn of
              Just insn -> return (insn, fromIntegral bytesRead)
              Nothing -> ET.throwError $ ARMInvalidInstruction segRelAddr contents
  else ET.throwError $ ARMMemoryError (MM.PermissionsError segRelAddr)

liftMemError :: Either (MM.MemoryError w) a -> Either (ARMMemoryError w) a
liftMemError e =
  case e of
    Left err -> Left (ARMMemoryError err)
    Right a -> Right a

-- | A wrapper around the 'MM.MemoryError' that lets us add in information about
-- invalid instructions.
data ARMMemoryError w = ARMInvalidInstruction !(MM.MemAddr w) [MM.MemChunk w]
                      | ARMMemoryError !(MM.MemoryError w)
                      | ARMInvalidInstructionAddress !(MM.MemSegment w) !(MM.MemWord w)
                      deriving (Show)

type LocatedError ppc ids = (Block ppc ids
                            , Int
                            , TranslationError (ArchAddrWidth ppc))

-- | This is a monad for error handling during disassembly
--
-- It allows for early failure that reports progress (in the form of blocks
-- discovered and the latest address examined) along with a reason for failure
-- (a 'TranslationError').
newtype DisM ppc ids s a = DisM { unDisM :: ET.ExceptT (LocatedError ppc ids) (ST s) a }
    deriving (Functor, Applicative, Monad)

-- | This funny instance is required because GHC doesn't allow type function
-- applications in instance heads, so we factor the type functions out into a
-- constraint on a fresh variable.  See
--
-- > https://stackoverflow.com/questions/45360959/illegal-type-synonym-family-application-in-instance-with-functional-dependency
--
-- We also can't derive this instance because of that restriction (but deriving
-- silently fails).
instance (w ~ ArchAddrWidth ppc) => ET.MonadError (Block ppc ids, Int, TranslationError w) (DisM ppc ids s) where
  throwError e = DisM (ET.throwError e)
  catchError a hdlr = do
    r <- liftST $ ET.runExceptT (unDisM a)
    case r of
      Left l -> do
        r' <- liftST $ ET.runExceptT (unDisM (hdlr l))
        case r' of
          Left e -> DisM (ET.throwError e)
          Right res -> return res
      Right res -> return res


data TranslationError w = TranslationError { transErrorAddr :: MM.MemSegmentOff w
                                           , transErrorReason :: TranslationErrorReason w
                                           }

data TranslationErrorReason w = InvalidNextPC (MM.MemAddr w) (MM.MemAddr w)
                              | DecodeError (ARMMemoryError w)
                              | UnsupportedInstruction InstructionSet
                              | InstructionAtUnmappedAddr InstructionSet
                              | GenerationError InstructionSet GeneratorError
                              deriving (Show)

deriving instance (MM.MemWidth w) => Show (TranslationError w)

liftST :: ST s a -> DisM arm ids s a
liftST = DisM . lift


-- | Early failure for 'DisM'.  This is a wrapper around 'ET.throwError' that
-- computes the current progress alongside the reason for the failure.
--
-- Note that the 'TranslateError' below is a block terminator marker that notes
-- that translation of the basic block resulted in an error (with the exception
-- string stored as its argument).  This allows macaw to carry errors in the
-- instruction stream, which is useful for debugging and diagnostics.
failAt :: forall arm ids s a
        . (ArchReg arm ~ ARMReg, MM.MemWidth (ArchAddrWidth arm))
       => GenState arm ids s
       -> MM.MemWord (ArchAddrWidth arm)
       -> MM.MemSegmentOff (ArchAddrWidth arm)
       -> TranslationErrorReason (ArchAddrWidth arm)
       -> DisM arm ids s a
failAt gs offset curPCAddr reason = do
  let exn = TranslationError { transErrorAddr = curPCAddr
                             , transErrorReason = reason
                             }
  let term = (`TranslateError` T.pack (show exn))
  let b = finishBlock' (gs ^. blockState) term
  ET.throwError (b, fromIntegral offset, exn)
