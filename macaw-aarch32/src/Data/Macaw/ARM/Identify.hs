-- | Provides functions used to identify calls and returns in the instructions.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.ARM.Identify
    ( identifyCall
    , identifyReturn
    , isReturnValue
    , conditionalReturnClassifier
    , conditionalCallClassifier
    ) where

import           Control.Applicative ( (<|>) )
import           Control.Lens ( (^.) )
import           Control.Monad ( when )
import qualified Control.Monad.Reader as CMR
import qualified Data.Foldable as F
import qualified Data.Macaw.ARM.ARMReg as AR
import qualified Data.Macaw.ARM.Arch as Arch
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery.Classifier as MDC
import qualified Data.Macaw.Discovery.ParsedContents as Parsed
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Macaw.SemMC.Simplify as MSS
import qualified Data.Macaw.Types as MT
import           Data.Maybe ( maybeToList )
import qualified Data.Sequence as Seq

import qualified SemMC.Architecture.AArch32 as ARM

import Prelude

-- | Test if an address is in an executable segment
isExecutableSegOff :: MC.MemSegmentOff w -> Bool
isExecutableSegOff sa =
  MC.segmentFlags (MC.segoffSegment sa) `MMP.hasPerm` MMP.execute

-- | This is a helper for 'identifyCall'
--
-- The call classifier just wants to know that the return address is a known
-- constant value, but doesn't really care what it is.  We could be more
-- specific and require it to be the next instruction, but that isn't really
-- necessary in practice.
--
-- In the most basic form, we would expect this to be a
-- 'MC.RelocatableValue'. However, in Thumb mode, the semantics do a bit of
-- extra work to force the low bit to be set. If the return address is not
-- obviously syntactically a 'MC.RelocatableValue', we traverse the term
-- expected form of the complex term to make sure it is what we expect for thumb
-- (and bottoms out in a known value).
isValidReturnAddress
  :: MC.Value ARM.AArch32 ids (MT.BVType 32)
  -> Maybe (MC.Value ARM.AArch32 ids (MT.BVType 32))
isValidReturnAddress val0 =
  case val0 of
    MC.RelocatableValue {} -> return val0
    _ -> do
      MC.BVOr _ val1 _ <- MC.valueAsApp val0
      MC.BVShl _ val2 _ <- MC.valueAsApp val1
      MC.UExt val3 _ <- MC.valueAsApp val2
      MC.Trunc val4 _ <- MC.valueAsApp val3
      MC.BVAnd _ val5 _ <- MC.valueAsApp val4
      MC.BVShr _ val6@(MC.RelocatableValue {}) _ <- MC.valueAsApp val5
      return val6
      <|> do
      MC.BVOr _ val1 _ <- MC.valueAsApp val0
      MC.BVShl _ val2 _ <- MC.valueAsApp val1
      MC.UExt val3 _ <- MC.valueAsApp val2
      MC.Trunc val4 _ <- MC.valueAsApp val3
      MC.BVShr _ val5@(MC.RelocatableValue {}) _ <- MC.valueAsApp val4
      return val5

-- | Identifies a call statement, *after* the corresponding statement
-- has been performed.  This can be tricky with ARM because there are
-- several instructions that can update R15 and effect a "call",
-- athough the predicate condition on those instructions can determine
-- if it is actually executed or not.  Also need to consider A32
-- v.s. T32 mode.
identifyCall :: MM.Memory (MC.ArchAddrWidth ARM.AArch32)
             -> Seq.Seq (MC.Stmt ARM.AArch32 ids)
             -> MC.RegState (MC.ArchReg ARM.AArch32) (MC.Value ARM.AArch32 ids)
             -> Maybe (Seq.Seq (MC.Stmt ARM.AArch32 ids), MC.ArchSegmentOff ARM.AArch32)
identifyCall mem stmts0 rs
  | Just retVal <- isValidReturnAddress (rs ^. MC.boundValue AR.arm_LR)
  , Just retAddrVal <- MC.valueAsMemAddr retVal
  , Just retAddr <- MM.asSegmentOff mem retAddrVal =
      Just (stmts0, retAddr)
  | otherwise = Nothing

-- | Intended to identify a return statement.
--
-- The current implementation is to attempt to recognize the Macaw
-- 'ReturnAddr' value (placed in the LR register by
-- 'mkInitialAbsState') when it is placed in the PC (instruction
-- pointer), but unfortunately this does not work because ARM
-- semantics will clear the low bit (T32 mode) or the low two bits
-- (A32 mode) when writing to the PC to discard the mode bit in target
-- addresses.
identifyReturn :: Seq.Seq (MC.Stmt ARM.AArch32 ids)
               -> MC.RegState (MC.ArchReg ARM.AArch32) (MC.Value ARM.AArch32 ids)
               -> MA.AbsProcessorState (MC.ArchReg ARM.AArch32) ids
               -> Maybe (Seq.Seq (MC.Stmt ARM.AArch32 ids))
identifyReturn stmts s finalRegSt8 =
  if isReturnValue finalRegSt8 (s^.MC.boundValue MC.ip_reg)
  then Just stmts
  else Nothing

-- | Determines if the supplied value is the symbolic return address
-- from Macaw, modulo any ARM semantics operations (lots of ite caused
-- by the conditional execution bits for most instructions, clearing
-- of the low bits (1 in T32 mode, 2 in A32 mode).
isReturnValue :: MA.AbsProcessorState (MC.ArchReg ARM.AArch32) ids
              -> MC.Value ARM.AArch32 ids (MT.BVType (MC.RegAddrWidth (MC.ArchReg ARM.AArch32)))
              -> Bool
isReturnValue absProcState val =
  case MA.transferValue absProcState val of
    MA.ReturnAddr -> True
    _ -> False

-- | If one of the values is the abstract return address, return the other (if it is a constant)
--
-- If neither is the abstract return address (or the other value is not a constant), return 'Nothing'
asReturnAddrAndConstant
  :: MC.Memory 32
  -> MA.AbsProcessorState (MC.ArchReg ARM.AArch32) ids
  -> MC.Value ARM.AArch32 ids (MT.BVType (MC.ArchAddrWidth ARM.AArch32))
  -> MC.Value ARM.AArch32 ids (MT.BVType (MC.ArchAddrWidth ARM.AArch32))
  -> MAI.Classifier (MC.ArchSegmentOff ARM.AArch32)
asReturnAddrAndConstant mem absProcState mRet mConstant = do
  MA.ReturnAddr <- return (MA.transferValue absProcState mRet)
  Just memAddr <- return (MC.valueAsMemAddr mConstant)
  Just segOff <- return (MC.asSegmentOff mem memAddr)
  when (not (isExecutableSegOff segOff)) $ do
    fail ("Conditional return successor is not executable: " ++ show memAddr)
  return segOff

-- | Simplify nested muxes if possible
--
-- If the term is a mux and cannot be simplified, return it unchanged.  If the
-- term is not a mux, return Nothing.
--
-- We need this because the terms generated by the conditional return
-- instructions seem to always include nested muxes, which we don't want to have
-- to match against in a brittle way.  The 'MSS.simplifyArchApp' function (for
-- AArch32) has that simplification. Note that some of the other simplification
-- entry points do *not* call that function, so it is important that we use this
-- entry point. We don't need the arithmetic simplifications provided by the
-- more general infrastructure.
simplifiedMux
  :: MSS.SimplifierExtension arch
  => MC.Value arch ids tp
  -> Maybe (MC.App (MC.Value arch ids) tp)
simplifiedMux ipVal
  | Just app@(MC.Mux {}) <- MC.valueAsApp ipVal =
      MSS.simplifyArchApp app <|> pure app
  | otherwise = Nothing

data ReturnsOnBranch = ReturnsOnTrue | ReturnsOnFalse
  deriving (Eq)

-- | Inspect the IP register to determine if this statement causes a conditional return
--
-- We expect a mux where one of the IP values is the abstract return address and
-- the other is an executable address.  Ideally we would be able to say that is
-- the "next" instruction address, but we do not have a good way to determine
-- the *current* instruction address. This just means that we have a more
-- flexible recognizer for conditional returns, even though there are
-- (probably?) no ARM instructions that could return that way.
--
-- The returned values are:
--
--  * The condition of the conditional return
--  * The next IP
--  * An indicator of which branch is the return branch
--  * The statements to use as the statement list
--
-- Note that we currently don't modify the statement list, but could
identifyConditionalReturn
  :: MC.Memory 32
  -> Seq.Seq (MC.Stmt ARM.AArch32 ids)
  -> MC.RegState (MC.ArchReg ARM.AArch32) (MC.Value ARM.AArch32 ids)
  -> MA.AbsProcessorState (MC.ArchReg ARM.AArch32) ids
  -> MAI.Classifier ( MC.Value ARM.AArch32 ids MT.BoolType
                    , MC.ArchSegmentOff ARM.AArch32
                    , ReturnsOnBranch
                    , Seq.Seq (MC.Stmt ARM.AArch32 ids)
                    )
identifyConditionalReturn mem stmts s finalRegState
  | not (null stmts)
  , Just (MC.Mux _ c t f) <- simplifiedMux (s ^. MC.boundValue MC.ip_reg) =
      case asReturnAddrAndConstant mem finalRegState t f of
        MAI.ClassifySucceeded _ nextIP -> return (c, nextIP, ReturnsOnTrue, stmts)
        MAI.ClassifyFailed _ -> do
          nextIP <- asReturnAddrAndConstant mem finalRegState f t
          return (c, nextIP, ReturnsOnFalse, stmts)
  | otherwise = fail "IP is not a mux"

-- | Recognize ARM conditional returns and generate an appropriate arch-specific
-- terminator
--
-- Conditional returns are not supported in core macaw, so we need to use an
-- arch-specific terminator.  Unlike simple arch-terminators, this one requires
-- analysis that can only happen in the context of a block classifier.
--
-- Note that there are two cases below that could be handled. It seems unlikely
-- that these would be produced in practice, so they are unhandled for now.
conditionalReturnClassifier :: MAI.BlockClassifier ARM.AArch32 ids
conditionalReturnClassifier = do
  stmts <- CMR.asks MAI.classifierStmts
  mem <- CMR.asks (MAI.pctxMemory . MAI.classifierParseContext)
  regs <- CMR.asks MAI.classifierFinalRegState
  absState <- CMR.asks MAI.classifierAbsState
  (cond, nextIP, returnBranch, stmts') <- MAI.liftClassifier (identifyConditionalReturn mem stmts regs absState)
  let term = if returnBranch == ReturnsOnTrue then Arch.ReturnIf cond else Arch.ReturnIfNot cond
  writtenAddrs <- CMR.asks MAI.classifierWrittenAddrs

  jmpBounds <- CMR.asks MAI.classifierJumpBounds
  ainfo <- CMR.asks (MAI.pctxArchInfo . MAI.classifierParseContext)

  case Jmp.postBranchBounds jmpBounds regs cond of
    Jmp.BothFeasibleBranch trueJumpState falseJumpState -> do
      -- Both branches are feasible, but we don't need the "true" case because
      -- it is actually a return
      let abs' = MDC.branchBlockState ainfo absState stmts regs cond (returnBranch == ReturnsOnFalse)
      let fallthroughTarget = ( nextIP
                              , abs'
                              , if returnBranch == ReturnsOnTrue then falseJumpState else trueJumpState
                              )
      return Parsed.ParsedContents { Parsed.parsedNonterm = F.toList stmts'
                                   , Parsed.parsedTerm = Parsed.ParsedArchTermStmt term regs (Just nextIP)
                                   , Parsed.intraJumpTargets = [fallthroughTarget]
                                   , Parsed.newFunctionAddrs = []
                                   , Parsed.writtenCodeAddrs = writtenAddrs
                                   }
    Jmp.TrueFeasibleBranch _ -> fail "Infeasible false branch"
    Jmp.FalseFeasibleBranch _ -> fail "Infeasible true branch"
    Jmp.InfeasibleBranch -> fail "Branch targets are both infeasible"

data CallsOnBranch = CallsOnTrue | CallsOnFalse
  deriving (Eq)

-- | Takes a conditionally-set PC and LR value pair and, if they are the same, returns the value
--
-- The observation backing this is that there are two cases for a conditional
-- call. First, assume that the condition evaluates to true (i.e., the call is
-- issued).  In that case, the fallthrough address (which would have been taken
-- if the condition was false) and the value in the LR should be the same
-- (modulo thumb mode switching).
--
-- The other case, assuming that the call is not taken, is symmetric.
--
-- As a result, the caller ('identifyConditionalCall') is expected to call this
-- twice, once with @(pc_t, lr_f)@ and again with @(pc_f, lr_t)@.
--
-- Note that this classifier helper does not use the abstract transfer function
-- because return addresses should be literals that don't need any interpretation.
asConditionalCallReturnAddress
  :: MC.Memory 32
  -> MC.Value ARM.AArch32 ids (MT.BVType (MC.ArchAddrWidth ARM.AArch32))
  -- ^ The value of the PC at one condition polarity
  -> MC.Value ARM.AArch32 ids (MT.BVType (MC.ArchAddrWidth ARM.AArch32))
  -- ^ The value of the LR at the other condition polarity
  -> MAI.Classifier (MC.ArchSegmentOff ARM.AArch32)
asConditionalCallReturnAddress mem pc_val lr_val = do
  Just memAddr_pc <- return (MC.valueAsMemAddr pc_val)
  Just memAddr_lr <- return (MC.valueAsMemAddr lr_val)
  Just segOff_pc <- return (MC.asSegmentOff mem memAddr_pc)
  Just segOff_lr <- return (MC.asSegmentOff mem memAddr_lr)
  when (not (segOff_pc == segOff_lr) || not (isExecutableSegOff segOff_lr)) $ do
    fail ("Conditional call return address is not executable: " ++ show (memAddr_lr))
  return segOff_lr

-- | This is a conditional call if the PC and LR are both muxes. Note that we
-- don't really care what the call target is (and cannot validate it, since it
-- could be a complex computed value). We primarily care that the conditional LR
-- value is a valid return address *and* is equal to one of the possible next PC
-- values.
--
-- Note that we return the condition on the PC and not the LR. Ideally they
-- should be the same, but we aren't currently checking that.
identifyConditionalCall
  :: MC.Memory 32
  -> Seq.Seq (MC.Stmt ARM.AArch32 ids)
  -> MC.RegState (MC.ArchReg ARM.AArch32) (MC.Value ARM.AArch32 ids)
  -> MAI.Classifier ( MC.Value ARM.AArch32 ids MT.BoolType    -- Condition
                    , MC.Value ARM.AArch32 ids (MT.BVType 32) -- Call target
                    , MC.Value ARM.AArch32 ids (MT.BVType 32) -- Raw link register value
                    , MC.ArchSegmentOff ARM.AArch32           -- Return address (also the fallthrough address) decoded into a segment offset
                    , CallsOnBranch                           -- Which branch the call actually occurs on
                    , Seq.Seq (MC.Stmt ARM.AArch32 ids)       -- The modified statement list
                    )
identifyConditionalCall mem stmts s
  | not (null stmts)
  , Just (MC.Mux _ pc_c pc_t pc_f) <- simplifiedMux (s ^. MC.boundValue MC.ip_reg)
  , Just (MC.Mux _ _lr_c lr_t lr_f) <- simplifiedMux (s ^. MC.boundValue AR.arm_LR) =
      case asConditionalCallReturnAddress mem pc_t lr_f of
        MAI.ClassifySucceeded _ nextIP ->
          return (pc_c, pc_f, lr_f, nextIP, CallsOnFalse, stmts)
        MAI.ClassifyFailed _ -> do
          nextIP <- asConditionalCallReturnAddress mem pc_f lr_t
          return (pc_c, pc_t, lr_t, nextIP, CallsOnTrue, stmts)
  | otherwise = fail "IP is not a mux"

extractCallTargets
  :: MC.Memory 32
  -> MC.Value ARM.AArch32 ids (MT.BVType 32)
  -> [MC.ArchSegmentOff ARM.AArch32]
extractCallTargets mem val =
  case val of
    MC.BVValue _ x -> maybeToList $ MM.resolveAbsoluteAddr mem (fromInteger x)
    MC.RelocatableValue _ a -> maybeToList $ MM.asSegmentOff mem a
    MC.SymbolValue {} -> []
    MC.AssignedValue {} -> []
    MC.Initial {} -> []

-- | Classify ARM-specific conditional calls
--
-- This has the same rationale as 'conditionalReturnClassifier'; core macaw does
-- not have a representation of conditional calls, so we need to introduce
-- architecture-specific terminators for them.
conditionalCallClassifier :: MAI.BlockClassifier ARM.AArch32 ids
conditionalCallClassifier = do
  stmts <- CMR.asks MAI.classifierStmts
  mem <- CMR.asks (MAI.pctxMemory . MAI.classifierParseContext)
  regs <- CMR.asks MAI.classifierFinalRegState
  absState <- CMR.asks MAI.classifierAbsState
  (cond, callTarget, returnAddr, fallthroughIP, callBranch, stmts') <- MAI.liftClassifier (identifyConditionalCall mem stmts regs)
  let term = if callBranch == CallsOnTrue
             then Arch.CallIf cond callTarget returnAddr
             else Arch.CallIfNot cond callTarget returnAddr
  writtenAddrs <- CMR.asks MAI.classifierWrittenAddrs
  jmpBounds <- CMR.asks MAI.classifierJumpBounds
  ainfo <- CMR.asks (MAI.pctxArchInfo . MAI.classifierParseContext)

  case Jmp.postBranchBounds jmpBounds regs cond of
    Jmp.BothFeasibleBranch trueJumpState falseJumpState -> do
      let abs' = MDC.branchBlockState ainfo absState stmts regs cond (callBranch == CallsOnFalse)
      let fallthroughTarget = ( fallthroughIP
                              , abs'
                              , if callBranch == CallsOnTrue then falseJumpState else trueJumpState
                              )
      return Parsed.ParsedContents { Parsed.parsedNonterm = F.toList stmts'
                                   , Parsed.parsedTerm = Parsed.ParsedArchTermStmt term regs (Just fallthroughIP)
                                   , Parsed.intraJumpTargets = [fallthroughTarget]
                                   , Parsed.newFunctionAddrs = extractCallTargets mem callTarget
                                   , Parsed.writtenCodeAddrs = writtenAddrs
                                   }
    Jmp.TrueFeasibleBranch _ -> fail "Infeasible false branch"
    Jmp.FalseFeasibleBranch _ -> fail "Infeasible true branch"
    Jmp.InfeasibleBranch -> fail "Branch targets are both infeasible"
