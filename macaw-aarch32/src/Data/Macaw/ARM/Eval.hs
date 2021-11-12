{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Macaw.ARM.Eval
    ( initialBlockRegs
    , mkInitialAbsState
    , extractBlockPrecond
    , absEvalArchFn
    , absEvalArchStmt
    , postARMTermStmtAbsState
    , preserveRegAcrossSyscall
    , callParams
    )
    where

import           Control.Lens ( (&), (^.), (.~) )
import qualified Data.Macaw.ARM.ARMReg as AR
import qualified Data.Macaw.ARM.Arch as AA
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.AbsDomain.JumpBounds as MJ
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.SemMC.Generator as MSG
import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Parameterized.NatRepr (knownNat)
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Set as Set

import qualified Language.ASL.Globals as ASL
import qualified SemMC.Architecture.AArch32 as ARM

import qualified Data.Macaw.ARM.Arch as MAA
import           Data.Macaw.ARM.Simplify ()

callParams :: (forall tp . AR.ARMReg tp -> Bool)
           -> MA.CallParams AR.ARMReg
callParams preservePred =
  MA.CallParams { MA.postCallStackDelta = 0
                , MA.preserveReg = preservePred
                , MA.stackGrowsDown = True
                }

-- FIXME: initialize some of the globals to FALSE
initialBlockRegs :: forall ids .
                    MC.ArchSegmentOff ARM.AArch32
                    -- ^ The address of the block
                 -> MC.ArchBlockPrecond ARM.AArch32
                 -> MC.RegState (MC.ArchReg ARM.AArch32) (MC.Value ARM.AArch32 ids)
initialBlockRegs addr preconds = MSG.initRegState addr &
  -- FIXME: Set all simple globals to 0??
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__BranchTaken")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__UnpredictableBehavior")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__UndefinedBehavior")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__AssertionFailure")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")) .~ boolAsBV (MAA.bpPSTATE_T preconds) &
  MC.boundValue (AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_IT")) .~ MC.BVValue knownNat 0 &
  MC.boundValue (AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_nRW")) .~ MC.BVValue knownNat 1 &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__PendingInterrupt")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__PendingPhysicalSError")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__Sleeping")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__BranchTaken")) .~ MC.BoolValue False
  where
    boolAsBV b = if b then MC.bvValue 1 else MC.bvValue 0

-- | We use the block precondition to propagate the value of PSTATE_T throughout
-- functions.
--
-- We consider it an error if PSTATE_T is not concrete. Technically we could
-- modify macaw to discover code with an abstract PSTATE_T as both T32 and A32,
-- but it isn't worth the complexity until we encounter it in the wild.
extractBlockPrecond :: MC.ArchSegmentOff ARM.AArch32
                    -> MA.AbsBlockState (MC.ArchReg ARM.AArch32)
                    -> Either String (MC.ArchBlockPrecond ARM.AArch32)
extractBlockPrecond _ absState =
  case absState ^. MA.absRegState . MC.boundValue (AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")) of
    MA.FinSet (Set.toList -> [bi]) -> Right (MAA.ARMBlockPrecond { MAA.bpPSTATE_T = bi == 1 })
    MA.FinSet {} -> Left "Multiple FinSet values for PSTATE_T"
    MA.StridedInterval {} -> Left "StridedInterval where PSTATE_T expected"
    MA.SubValue {} -> Left "SubValue where PSTATE_T expected"
    MA.TopV -> Left "TopV where PSTATE_T expected"

-- | Set up an initial abstract state that holds at the beginning of a function.
--
-- The 'MM.Memory' is the mapped memory region
--
-- The 'ArchSegmentOff' is the start address of the basic block.
--
-- Note that we don't initialize the abstract stack.  On ARM, there are no
-- initial stack entries (since the return address is in the link register).
--
-- We set the initial @PSTATE_T@ for a function based on the low bit of its
-- address.
mkInitialAbsState :: MM.Memory 32
                  -> MC.ArchSegmentOff ARM.AArch32
                  -> MA.AbsBlockState (MC.ArchReg ARM.AArch32)
mkInitialAbsState _mem startAddr =
  s0 & MA.absRegState . MC.boundValue AR.arm_LR .~ MA.ReturnAddr
     & MA.absRegState . MC.boundValue pstate_t_reg .~ MA.FinSet (Set.fromList [pstate_t_val])
  -- FIXME: Initialize every single global to macaw's "Initial" value
  where initRegVals = MapF.fromList []
        s0 = MA.fnStartAbsBlockState startAddr initRegVals []
        pstate_t_reg = AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")
        pstate_t_val = if lowBitSet startAddr then 1 else 0

lowBitSet :: MC.ArchSegmentOff ARM.AArch32 -> Bool
lowBitSet addr = MC.clearSegmentOffLeastBit addr /= addr

absEvalArchFn :: MA.AbsProcessorState (MC.ArchReg ARM.AArch32) ids
              -> MC.ArchFn ARM.AArch32 (MC.Value ARM.AArch32 ids) tp
              -> MA.AbsValue 32 tp
absEvalArchFn _r f =
  case f of
    AA.UDiv{} -> MA.TopV
    AA.SDiv{} -> MA.TopV
    AA.URem{} -> MA.TopV
    AA.SRem{} -> MA.TopV
    AA.UnsignedRSqrtEstimate {} -> MA.TopV
    AA.FPSub {} -> MA.TopV
    AA.FPAdd {} -> MA.TopV
    AA.FPMul {} -> MA.TopV
    AA.FPDiv {} -> MA.TopV
    AA.FPRecipEstimate {} -> MA.TopV
    AA.FPRecipStep {} -> MA.TopV
    AA.FPSqrtEstimate {} -> MA.TopV
    AA.FPRSqrtStep {} -> MA.TopV
    AA.FPSqrt {} -> MA.TopV
    AA.FPMax {} -> MA.TopV
    AA.FPMin {} -> MA.TopV
    AA.FPMaxNum {} -> MA.TopV
    AA.FPMinNum {} -> MA.TopV
    AA.FPMulAdd {} -> MA.TopV
    AA.FPCompareGE {} -> MA.TopV
    AA.FPCompareGT {} -> MA.TopV
    AA.FPCompareEQ {} -> MA.TopV
    AA.FPCompareNE {} -> MA.TopV
    AA.FPCompareUN {} -> MA.TopV
    AA.FPToFixed {} -> MA.TopV
    AA.FixedToFP {} -> MA.TopV
    AA.FPConvert {} -> MA.TopV
    AA.FPToFixedJS {} -> MA.TopV
    AA.FPRoundInt {} -> MA.TopV

-- For now, none of the architecture-specific statements have an effect on the
-- abstract value.
absEvalArchStmt :: MA.AbsProcessorState (MC.ArchReg ARM.AArch32) ids
                -> MC.ArchStmt ARM.AArch32 (MC.Value ARM.AArch32 ids)
                -> MA.AbsProcessorState (MC.ArchReg ARM.AArch32) ids
absEvalArchStmt s _ = s


postARMTermStmtAbsState :: (forall tp . AR.ARMReg tp -> Bool)
                        -> MM.Memory 32
                        -> MA.AbsProcessorState AR.ARMReg ids
                        -> MJ.IntraJumpBounds ARM.AArch32 ids
                        -> MC.RegState AR.ARMReg (MC.Value ARM.AArch32 ids)
                        -> AA.ARMTermStmt ids
                        -> Maybe (MM.MemSegmentOff 32, MA.AbsBlockState AR.ARMReg, MJ.InitJumpBounds ARM.AArch32)
postARMTermStmtAbsState preservePred mem s0 jumpBounds regState stmt =
  case stmt of
    AA.ARMSyscall _ ->
      case simplifyValue (regState ^. MC.curIP) of
        Just (MC.RelocatableValue _ addr)
          | Just nextPC <- MM.asSegmentOff mem (MM.incAddr 4 addr) -> do
              let params = MA.CallParams { MA.postCallStackDelta = 0
                                         , MA.preserveReg = preservePred
                                         , MA.stackGrowsDown = True
                                         }
              Just (nextPC, MA.absEvalCall params s0 regState nextPC, MJ.postCallBounds params jumpBounds regState)
        _ -> error ("Syscall could not interpret next PC: " ++ show (regState ^. MC.curIP))
    AA.ThumbSyscall _ ->
      case simplifyValue (regState ^. MC.curIP) of
        Just (MC.RelocatableValue _ addr)
          | Just nextPC <- MM.asSegmentOff mem (MM.incAddr 2 addr) -> do
              let params = MA.CallParams { MA.postCallStackDelta = 0
                                         , MA.preserveReg = preservePred
                                         , MA.stackGrowsDown = True
                                         }
              Just (nextPC, MA.absEvalCall params s0 regState nextPC, MJ.postCallBounds params jumpBounds regState)
        _ -> error ("Syscall could not interpret next PC: " ++ show (regState ^. MC.curIP))
    AA.ReturnIf _ ->
      case simplifyValue (regState ^. MC.curIP) of
        Just (MC.RelocatableValue _ addr)
          | Just nextPC <- MM.asSegmentOff mem (MM.incAddr 4 addr) -> do
              let params = MA.CallParams { MA.postCallStackDelta = 0
                                         , MA.preserveReg = preservePred
                                         , MA.stackGrowsDown = True
                                         }
              Just (nextPC, MA.absEvalCall params s0 regState nextPC, MJ.postCallBounds params jumpBounds regState)
        _ -> error ("Syscall could not interpret next PC: " ++ show (regState ^. MC.curIP))
    AA.ReturnIfNot _ ->
      case simplifyValue (regState ^. MC.curIP) of
        Just (MC.RelocatableValue _ addr)
          | Just nextPC <- MM.asSegmentOff mem (MM.incAddr 4 addr) -> do
              let params = MA.CallParams { MA.postCallStackDelta = 0
                                         , MA.preserveReg = preservePred
                                         , MA.stackGrowsDown = True
                                         }
              Just (nextPC, MA.absEvalCall params s0 regState nextPC, MJ.postCallBounds params jumpBounds regState)
        _ -> error ("Syscall could not interpret next PC: " ++ show (regState ^. MC.curIP))

preserveRegAcrossSyscall :: MC.ArchReg ARM.AArch32 tp -> Bool
preserveRegAcrossSyscall r =
  Some r `Set.member` AR.linuxSystemCallPreservedRegisters
