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
import qualified Data.Sequence as Seq

import qualified SemMC.Architecture.AArch32 as ARM

import           Data.Macaw.ARM.Simplify ()

import Prelude

isExecutableSegOff :: MC.MemSegmentOff w -> Bool
isExecutableSegOff sa =
  MC.segmentFlags (MC.segoffSegment sa) `MMP.hasPerm` MMP.execute

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
  | not (null stmts0)
  , MC.RelocatableValue {} <- rs ^. MC.boundValue AR.arm_LR
  , Just retVal <- MSS.simplifyValue (rs ^. MC.boundValue AR.arm_LR)
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
  -> Maybe (MC.ArchSegmentOff ARM.AArch32)
asReturnAddrAndConstant mem absProcState mRet mConstant = do
  MA.ReturnAddr <- return (MA.transferValue absProcState mRet)
  memAddr <- MC.valueAsMemAddr mConstant
  segOff <- MC.asSegmentOff mem memAddr
  when (not (isExecutableSegOff segOff)) $ do
    fail ("Conditional return successor is not executable: " ++ show memAddr)
  return segOff

simplifiedMux
  :: MSS.SimplifierExtension arch
  => MC.Value arch ids tp
  -> Maybe (MC.App (MC.Value arch ids) tp)
simplifiedMux ipVal
  | Just app@(MC.Mux {}) <- MC.valueAsApp ipVal =
      MSS.simplifyArchApp app <|> pure app
  | otherwise = Nothing

identifyConditionalReturn
  :: MC.Memory 32
  -> Seq.Seq (MC.Stmt ARM.AArch32 ids)
  -> MC.RegState (MC.ArchReg ARM.AArch32) (MC.Value ARM.AArch32 ids)
  -> MA.AbsProcessorState (MC.ArchReg ARM.AArch32) ids
  -> Maybe ( MC.Value ARM.AArch32 ids MT.BoolType
           , MC.ArchSegmentOff ARM.AArch32
           , Bool
           , Seq.Seq (MC.Stmt ARM.AArch32 ids)
           )
identifyConditionalReturn mem stmts s finalRegState
  | not (null stmts)
  , Just (MC.Mux _ c t f) <- simplifiedMux (s ^. MC.boundValue MC.ip_reg) =
      case asReturnAddrAndConstant mem finalRegState t f of
        Just nextIP -> return (c, nextIP, False, stmts)
        Nothing -> do
          nextIP <- asReturnAddrAndConstant mem finalRegState f t
          return (c, nextIP, True, stmts)
  | otherwise = Nothing

conditionalReturnClassifier :: MAI.BlockClassifier ARM.AArch32 ids
conditionalReturnClassifier = do
  stmts <- CMR.asks MAI.classifierStmts
  mem <- CMR.asks (MAI.pctxMemory . MAI.classifierParseContext)
  regs <- CMR.asks MAI.classifierFinalRegState
  absState <- CMR.asks MAI.classifierAbsState
  Just (cond, nextIP, fallthroughBranch, stmts') <- return (identifyConditionalReturn mem stmts regs absState)
  let term = if fallthroughBranch then Arch.ReturnIfNot cond else Arch.ReturnIf cond
  writtenAddrs <- CMR.asks MAI.classifierWrittenAddrs

  jmpBounds <- CMR.asks MAI.classifierJumpBounds
  ainfo <- CMR.asks (MAI.pctxArchInfo . MAI.classifierParseContext)

  case Jmp.postBranchBounds jmpBounds regs cond of
    Jmp.BothFeasibleBranch trueJumpState falseJmpState -> do
      -- Both branches are feasible, but we don't need the "true" case because
      -- it is actually a return
      let abs' = MDC.branchBlockState ainfo absState stmts regs cond fallthroughBranch
      let fallthroughTarget = ( nextIP
                              , abs'
                              , if fallthroughBranch then trueJumpState else falseJmpState
                              )
      return Parsed.ParsedContents { Parsed.parsedNonterm = F.toList stmts'
                                   , Parsed.parsedTerm = Parsed.ParsedArchTermStmt term regs (Just nextIP)
                                   , Parsed.intraJumpTargets = [fallthroughTarget]
                                   , Parsed.newFunctionAddrs = []
                                   , Parsed.writtenCodeAddrs = writtenAddrs
                                   }
    Jmp.InfeasibleBranch -> fail "Branch targets are both infeasible"
