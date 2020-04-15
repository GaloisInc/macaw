{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

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
import qualified Data.Macaw.Architecture.Info as MI
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
initialBlockRegs addr _preconds = MSG.initRegState addr &
  -- FIXME: Set all simple globals to 0??
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__BranchTaken")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__UnpredictableBehavior")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__UndefinedBehavior")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__AssertionFailure")) .~ MC.BoolValue False &
  -- FIXME: PSTATE_T is 0 for ARM mode, 1 for Thumb mode. For now, we
  -- are setting this concretely to 0 at the start of a block, but
  -- once we get Thumb support, we will want to refer to the semantics
  -- for this.
  MC.boundValue (AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")) .~ MC.BVValue knownNat 0 &
  MC.boundValue AR.ARMWriteMode .~ MC.BVValue knownNat 0 &
  MC.boundValue (AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_IT")) .~ MC.BVValue knownNat 0 &
  MC.boundValue (AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_T")) .~ MC.BVValue knownNat 0 &
  MC.boundValue (AR.ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_nRW")) .~ MC.BVValue knownNat 1 &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__PendingInterrupt")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__PendingPhysicalSError")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__Sleeping")) .~ MC.BoolValue False &
  MC.boundValue (AR.ARMGlobalBool (ASL.knownGlobalRef @"__BranchTaken")) .~ MC.BoolValue False


extractBlockPrecond :: MC.ArchSegmentOff ARM.AArch32
                    -> MA.AbsBlockState (MC.ArchReg ARM.AArch32)
                    -> Either String (MI.ArchBlockPrecond ARM.AArch32)
extractBlockPrecond _ _ = Right ()

-- | Set up an initial abstract state that holds at the beginning of a function.
--
-- The 'MM.Memory' is the mapped memory region
--
-- The 'ArchSegmentOff' is the start address of the basic block.
--
-- Note that we don't initialize the abstract stack.  On ARM, there are no
-- initial stack entries (since the return address is in the link register).
--
mkInitialAbsState :: MM.Memory 32
                  -> MC.ArchSegmentOff ARM.AArch32
                  -> MA.AbsBlockState (MC.ArchReg ARM.AArch32)
mkInitialAbsState _mem startAddr =
  s0 & MA.absRegState . MC.boundValue AR.arm_LR .~ MA.ReturnAddr
  -- FIXME: Initialize every single global to macaw's "Initial" value
  where initRegVals = MapF.fromList []
        s0 = MA.fnStartAbsBlockState startAddr initRegVals []


absEvalArchFn :: MA.AbsProcessorState (MC.ArchReg ARM.AArch32) ids
              -> MC.ArchFn ARM.AArch32 (MC.Value ARM.AArch32 ids) tp
              -> MA.AbsValue 32 tp
absEvalArchFn _r f =
  case f of
    AA.UDiv{} -> MA.TopV
    AA.SDiv{} -> MA.TopV
    AA.URem{} -> MA.TopV
    AA.SRem{} -> MA.TopV

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
    -- FIXME: Check semantics for SVC. Is there a special function
    -- that we need to translate?
    -- ThumbSyscall _ ->
    --   case simplifyValue (regState^.curIP) of
    --     Just (RelocatableValue _ addr)
    --       | Just nextPC <- MM.asSegmentOff mem (MM.incAddr 2 addr) -> do
    --           let params = MA.CallParams { MA.postCallStackDelta = 0
    --                                      , MA.preserveReg = preservePred
    --                                      }
    --           Just (nextPC, MA.absEvalCall params s0 regState nextPC)
    --     _ -> error ("Syscall could not interpret next PC: " ++ show (regState ^. curIP))


preserveRegAcrossSyscall :: MC.ArchReg ARM.AArch32 tp -> Bool
preserveRegAcrossSyscall r =
  Some r `Set.member` AR.linuxSystemCallPreservedRegisters
