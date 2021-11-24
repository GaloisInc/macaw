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
present time, only the first two are supported by macaw-aarch32
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
    the ISETSTATE changes.

  * The macaw-base functionality will then create a block up to this
    point, and the FetchAndExecute status will cause the instructions
    at this point to be declared as another frontier for subsequent
    block discovery.  The AbsProcessorState associated with this
    frontier will inform the subsequent call to disassemblyFn which
    ISETSTATE is applicable for that disassembly.

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
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Macaw.ARM.ARMReg as AR
import           Data.Macaw.ARM.Arch()
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MCB
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Macaw.SemMC.Generator as SG
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.Nonce as NC
import qualified Data.Text as T
import qualified Dismantle.ARM.A32 as ARMD
import qualified Dismantle.ARM.T32 as ThumbD
import qualified Language.ASL.Globals as ASL
import           Text.Printf ( printf )

import qualified SemMC.Architecture.AArch32 as ARM

data InstructionSet = A32I ARMD.Instruction | T32I ThumbD.Instruction
                      deriving (Eq, Show)


-- | Disassemble a block from the given start address (which points into the
-- 'MM.Memory').
--
-- Return a list of disassembled blocks as well as the total number of bytes
-- occupied by those blocks.
disassembleFn :: (MC.Value ARM.AArch32 ids (MT.BVType 32) -> ARMD.Instruction -> Maybe (SG.Generator ARM.AArch32 ids s ()))
              -- ^ A function to look up the semantics for an A32 instruction.  The
              -- lookup is provided with the value of the IP in case IP-relative
              -- addressing is necessary.
              -> (MC.Value ARM.AArch32 ids (MT.BVType 32) -> ThumbD.Instruction -> Maybe (SG.Generator ARM.AArch32 ids s ()))
              -- ^ A function to look up the semantics for a T32 instruction.  The
              -- lookup is provided with the value of the IP in case IP-relative
              -- addressing is necessary.
              -> NC.NonceGenerator (ST s) ids
              -- ^ A generator of unique IDs used for assignments
              -> MC.ArchSegmentOff ARM.AArch32
              -- ^ The address to disassemble from
              -> (MC.RegState AR.ARMReg (MC.Value ARM.AArch32 ids))
              -- ^ The initial registers
              -> Int
              -- ^ Maximum size of the block (a safeguard)
              -> ST s (MCB.Block ARM.AArch32 ids, Int)
disassembleFn lookupA32Semantics lookupT32Semantics nonceGen startAddr regState maxSize = do
  -- NOTE: The core discovery loop passes in an initial register state with the
  -- PSTATE_T (thumb state) bit set or not set based on the predecessor blocks.
  -- However, that does not account for mode switches between function calls
  -- (because macaw does not maintain abstract states between function calls).
  -- We account for that by force setting PSTATE_T to 1 (true) if the low bit of
  -- the address is set.  Otherwise, we take the initial value.
  let dmode = thumbState regState
  let lookupSemantics ipval instr = case instr of
                                      A32I inst -> lookupA32Semantics ipval inst
                                      T32I inst -> lookupT32Semantics ipval inst
  mr <- ET.runExceptT (unDisM (tryDisassembleBlock
                               dmode
                               lookupSemantics
                               nonceGen (MC.clearSegmentOffLeastBit startAddr) regState maxSize))
  case mr of
    Left (blocks, off, _exn) -> return (blocks, off)
    Right (blocks, bytes) -> return (blocks, bytes)

-- | The mode we are decoding this block in (ARM vs Thumb)
--
-- We turn this into an explicit data type so that we don't need to check the
-- low bit of the address or PSTATE everywhere.
data DecodeMode = A32 | T32
  deriving (Show)

-- | If the low-bit of the address is set
thumbState :: MC.RegState AR.ARMReg (MC.Value ARM.AArch32 ids)
           -> DecodeMode
thumbState regState =
  let pstate_t_val = regState ^. MC.boundValue pstate_t
  in if pstate_t_val == MC.BVValue PN.knownNat 0 then A32 else T32
  where
    pstate_t = AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")

tryDisassembleBlock :: DecodeMode
                    -> (MC.Value ARM.AArch32 ids (MT.BVType 32) -> InstructionSet -> Maybe (SG.Generator ARM.AArch32 ids s ()))
                    -> NC.NonceGenerator (ST s) ids
                    -> MC.ArchSegmentOff ARM.AArch32
                    -> MC.RegState AR.ARMReg (MC.Value ARM.AArch32 ids)
                    -> Int
                    -> DisM ids s (MCB.Block ARM.AArch32 ids, Int)
tryDisassembleBlock dmode lookupSemantics nonceGen startAddr regState maxSize = do
  let gs0 = SG.initGenState nonceGen startAddr regState
  let startOffset = MM.segoffOffset startAddr
  (nextPCOffset, block) <- disassembleBlock dmode lookupSemantics gs0 startAddr 0 (startOffset + fromIntegral maxSize)
  unless (nextPCOffset > startOffset) $ do
    let reason = InvalidNextPC (MM.absoluteAddr nextPCOffset) (MM.absoluteAddr startOffset)
    failAt gs0 0 startAddr reason
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
disassembleBlock :: forall ids s
                  . DecodeMode
                 -> (MC.Value ARM.AArch32 ids (MT.BVType 32) -> InstructionSet -> Maybe (SG.Generator ARM.AArch32 ids s ()))
                 -- ^ A function to look up the semantics for an instruction that we disassemble
                 -> SG.GenState ARM.AArch32 ids s
                 -> MM.MemSegmentOff 32
                 -- ^ The current instruction pointer
                 -> MM.MemWord 32
                 -- ^ The offset into the block of this instruction
                 -> MM.MemWord 32
                 -- ^ The maximum offset into the bytestring that we should
                 -- disassemble to; in principle, macaw can tell us to limit our
                 -- search with this.
                 -> DisM ids s (MM.MemWord 32, MCB.Block ARM.AArch32 ids)
disassembleBlock dmode lookupSemantics gs curPCAddr blockOff maxOffset = do
  let seg = MM.segoffSegment curPCAddr
  let off = MM.segoffOffset curPCAddr
  case readInstruction dmode curPCAddr of
    Left err -> failAt gs blockOff curPCAddr (DecodeError err)
    Right (_, 0) -> failAt gs blockOff curPCAddr (InvalidNextPC (MM.segoffAddr curPCAddr) (MM.segoffAddr curPCAddr))
    Right (i, bytesRead) -> do
      -- traceM (show (curPCAddr, "II: ", show i))
      let nextPCOffset = off + bytesRead
          nextPC = MM.segmentOffAddr seg nextPCOffset
          nextPCVal :: MC.Value ARM.AArch32 ids (MT.BVType 32) = MC.RelocatableValue (MM.addrWidthRepr curPCAddr) nextPC
      -- Note: In ARM, the IP is incremented *after* an instruction
      -- executes; pass in the physical address of the instruction here.
      let ipVal = MC.BVValue (PN.knownNat @32) (fromIntegral (MM.addrOffset (MM.segoffAddr curPCAddr)))
      case lookupSemantics ipVal i of
        Nothing -> failAt gs blockOff curPCAddr (UnsupportedInstruction i)
        Just transformer -> do
          -- Once we have the semantics for the instruction (represented by a
          -- state transformer), we apply the state transformer and then extract
          -- a result from the state of the 'Generator'.
          egs1 <- liftST $ ET.runExceptT (SG.runGenerator SG.unfinishedBlock gs $ do
            let lineStr = printf "%s: %s" (show curPCAddr) (show (case i of
                                                                    A32I i' -> ARMD.ppInstruction i'
                                                                    T32I i' -> ThumbD.ppInstruction i'))
            SG.addStmt (MC.InstructionStart blockOff (T.pack lineStr))
            SG.addStmt (MC.Comment (T.pack  lineStr))
            SG.setRegVal AR.branchTaken (MC.CValue (MC.BoolCValue False))
            SG.asAtomicStateUpdate (MM.segoffAddr curPCAddr) transformer)
          case egs1 of
            Left genErr -> failAt gs blockOff curPCAddr (GenerationError i genErr)
            Right gs1 -> do
              case gs1 of
                SG.UnfinishedPartialBlock preBlock ->
                  if | MC.CValue (MC.BoolCValue False) <- preBlock ^. (SG.pBlockState . MC.boundValue AR.branchTakenReg)
                     , Just nextPCSegAddr <- MM.incSegmentOff curPCAddr (fromIntegral bytesRead) -> do
                    -- If the branch taken flag is anything besides a
                    -- concrete False value, then we are at the end of a
                    -- block.
                      let preBlock' = (SG.pBlockState . MC.curIP .~ nextPCVal) preBlock
                      let gs2 = SG.GenState { SG.assignIdGen = SG.assignIdGen gs
                                            , SG._blockState = preBlock'
                                            , SG.genAddr = nextPCSegAddr
                                            , SG.genRegUpdates = MapF.empty
                                            , SG._blockStateSnapshot = preBlock' ^. SG.pBlockState
                                            , SG.appCache = SG.appCache gs
                                            }
                      disassembleBlock dmode lookupSemantics gs2 nextPCSegAddr (blockOff + fromIntegral bytesRead) maxOffset
                     -- Otherwise, we are still at the end of a block.
                     | otherwise -> return (nextPCOffset, SG.finishBlock' preBlock MCB.FetchAndExecute)
                SG.FinishedPartialBlock b -> return (nextPCOffset, b)

-- | Read one instruction from the 'MM.Memory' at the given segmented offset.
--
-- Returns the instruction and number of bytes consumed /or/ an error.
--
-- This code assumes that the 'MM.ByteRegion' is maximal; that is, that there
-- are no byte regions that could be coalesced.
readInstruction :: (MM.MemWidth w)
                => DecodeMode
                -> MM.MemSegmentOff w
                -> Either (ARMMemoryError w) (InstructionSet, MM.MemWord w)
readInstruction dmode addr = do
  let seg = MM.segoffSegment addr
  let segRelAddr = MM.segoffAddr addr
  let alignedMsegOff = MM.clearSegmentOffLeastBit addr
  if MM.segmentFlags seg `MMP.hasPerm` MMP.execute
  then do
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
            let (bytesRead, minsn) = case dmode of
                                       A32 -> fmap (fmap A32I) $ ARMD.disassembleInstruction (LBS.fromStrict bs)
                                       T32 -> fmap (fmap T32I) $ ThumbD.disassembleInstruction (LBS.fromStrict bs)
            case minsn of
              Just insn -> return (insn, fromIntegral bytesRead)
              Nothing -> ET.throwError $ ARMInvalidInstruction dmode segRelAddr contents
  else ET.throwError $ ARMMemoryError (MM.PermissionsError segRelAddr)

liftMemError :: Either (MM.MemoryError w) a -> Either (ARMMemoryError w) a
liftMemError e =
  case e of
    Left err -> Left (ARMMemoryError err)
    Right a -> Right a

-- | A wrapper around the 'MM.MemoryError' that lets us add in information about
-- invalid instructions.
data ARMMemoryError w = ARMInvalidInstruction DecodeMode !(MM.MemAddr w) [MM.MemChunk w]
                      | ARMMemoryError !(MM.MemoryError w)
                      | ARMInvalidInstructionAddress !(MM.MemSegment w) !(MM.MemWord w)
                      deriving (Show)

type LocatedError ids = ( MCB.Block ARM.AArch32 ids
                        , Int
                        , TranslationError 32
                        )

-- | This is a monad for error handling during disassembly
--
-- It allows for early failure that reports progress (in the form of blocks
-- discovered and the latest address examined) along with a reason for failure
-- (a 'TranslationError').
newtype DisM ids s a = DisM { unDisM :: ET.ExceptT (LocatedError ids) (ST s) a }
    deriving (Functor, Applicative, Monad)

-- | This funny instance is required because GHC doesn't allow type function
-- applications in instance heads, so we factor the type functions out into a
-- constraint on a fresh variable.  See
--
-- > https://stackoverflow.com/questions/45360959/illegal-type-synonym-family-application-in-instance-with-functional-dependency
--
-- We also can't derive this instance because of that restriction (but deriving
-- silently fails).
instance ET.MonadError (MCB.Block ARM.AArch32 ids, Int, TranslationError 32) (DisM ids s) where
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
                              | GenerationError InstructionSet SG.GeneratorError
                              deriving (Show)

deriving instance (MM.MemWidth w) => Show (TranslationError w)

liftST :: ST s a -> DisM ids s a
liftST = DisM . lift


-- | Early failure for 'DisM'.  This is a wrapper around 'ET.throwError' that
-- computes the current progress alongside the reason for the failure.
--
-- Note that the 'TranslateError' below is a block terminator marker that notes
-- that translation of the basic block resulted in an error (with the exception
-- string stored as its argument).  This allows macaw to carry errors in the
-- instruction stream, which is useful for debugging and diagnostics.
failAt :: forall ids s a
        . SG.GenState ARM.AArch32 ids s
       -> MM.MemWord 32
       -> MM.MemSegmentOff 32
       -> TranslationErrorReason 32
       -> DisM ids s a
failAt gs bytesConsumed curPCAddr reason = do
  let exn = TranslationError { transErrorAddr = curPCAddr
                             , transErrorReason = reason
                             }
  let term = (`MCB.TranslateError` T.pack (show exn))
  let b = SG.finishBlock' (gs ^. SG.blockState) term
  ET.throwError (b, fromIntegral bytesConsumed, exn)
