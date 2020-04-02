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
import           Data.Macaw.ARM.ARMReg
import           Data.Macaw.ARM.Arch
import           Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.Architecture.Info as MI
import           Data.Macaw.CFG
import qualified Data.Macaw.AbsDomain.JumpBounds as MJ
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.SemMC.Generator as MSG
import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Parameterized.NatRepr (knownNat)
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Set as Set
import           GHC.TypeLits

import qualified Language.ASL.Globals as ASL
import qualified SemMC.Architecture.AArch32 as ARM

callParams :: (forall tp . ARMReg tp -> Bool)
           -> MA.CallParams ARMReg
callParams preservePred =
  MA.CallParams { MA.postCallStackDelta = 0
                , MA.preserveReg = preservePred
                , MA.stackGrowsDown = True
                }

-- FIXME: initialize some of the globals to FALSE
initialBlockRegs :: forall ids .
                    ArchSegmentOff ARM.AArch32
                    -- ^ The address of the block
                 -> ArchBlockPrecond ARM.AArch32
                 -> RegState (ArchReg ARM.AArch32) (Value ARM.AArch32 ids)
initialBlockRegs addr _preconds = MSG.initRegState addr &
  -- FIXME: Set all simple globals to 0??
  boundValue (ARMGlobalBool (ASL.knownGlobalRef @"__UnpredictableBehavior")) .~ BoolValue False &
  boundValue (ARMGlobalBool (ASL.knownGlobalRef @"__UndefinedBehavior")) .~ BoolValue False &
  boundValue (ARMGlobalBool (ASL.knownGlobalRef @"__AssertionFailure")) .~ BoolValue False &
  boundValue (ARMGlobalBV (ASL.knownGlobalRef @"PSTATE_IT")) .~ BVValue knownNat 0 &
  boundValue (ARMGlobalBool (ASL.knownGlobalRef @"__PendingInterrupt")) .~ BoolValue False &
  boundValue (ARMGlobalBool (ASL.knownGlobalRef @"__PendingPhysicalSError")) .~ BoolValue False &
  boundValue (ARMGlobalBool (ASL.knownGlobalRef @"__Sleeping")) .~ BoolValue False

extractBlockPrecond :: ArchSegmentOff ARM.AArch32
                    -> MA.AbsBlockState (ArchReg ARM.AArch32)
                    -> Either String (MI.ArchBlockPrecond ARM.AArch32)
extractBlockPrecond _ _ = Right ()

-- | Set up an initial abstract state that holds at the beginning of a basic
-- block.
--
-- The 'MM.Memory' is the mapped memory region
--
-- The 'ArchSegmentOff' is the start address of the basic block.
--
-- Note that we don't initialize the abstract stack.  On ARM, there are no
-- initial stack entries (since the return address is in the link register).
--
mkInitialAbsState :: MM.Memory (RegAddrWidth (ArchReg ARM.AArch32))
                  -> ArchSegmentOff ARM.AArch32
                  -> MA.AbsBlockState (ArchReg ARM.AArch32)
mkInitialAbsState _mem startAddr =
  s0 & MA.absRegState . boundValue arm_LR .~ MA.ReturnAddr
  -- FIXME: Initialize every single global to macaw's "Initial" value
  where initRegVals = MapF.fromList []
        s0 = MA.fnStartAbsBlockState startAddr initRegVals []


absEvalArchFn :: AbsProcessorState (ArchReg ARM.AArch32) ids
              -> ArchFn ARM.AArch32 (Value ARM.AArch32 ids) tp
              -> AbsValue (RegAddrWidth (ArchReg ARM.AArch32)) tp
absEvalArchFn _r f =
  case f of
    UDiv{} -> MA.TopV
    SDiv{} -> MA.TopV
    URem{} -> MA.TopV
    SRem{} -> MA.TopV

-- For now, none of the architecture-specific statements have an effect on the
-- abstract value.
absEvalArchStmt :: AbsProcessorState (ArchReg ARM.AArch32) ids
                -> ArchStmt ARM.AArch32 (Value ARM.AArch32 ids)
                -> AbsProcessorState (ArchReg ARM.AArch32) ids
absEvalArchStmt s _ = s


postARMTermStmtAbsState :: (forall tp . ARMReg tp -> Bool)
                        -> MM.Memory (RegAddrWidth (ArchReg ARM.AArch32))
                        -> AbsProcessorState ARMReg ids
                        -> MJ.IntraJumpBounds ARM.AArch32 ids
                        -> RegState ARMReg (Value ARM.AArch32 ids)
                        -> ARMTermStmt ids
                        -> Maybe (MM.MemSegmentOff (RegAddrWidth (ArchReg ARM.AArch32)), AbsBlockState ARMReg, MJ.InitJumpBounds ARM.AArch32)
postARMTermStmtAbsState preservePred mem s0 jumpBounds regState stmt =
  case stmt of
    ARMSyscall _ ->
      case simplifyValue (regState ^. curIP) of
        Just (RelocatableValue _ addr)
          | Just nextPC <- MM.asSegmentOff mem (MM.incAddr 4 addr) -> do
              let params = MA.CallParams { MA.postCallStackDelta = 0
                                         , MA.preserveReg = preservePred
                                         , MA.stackGrowsDown = True
                                         }
              Just (nextPC, MA.absEvalCall params s0 regState nextPC, MJ.postCallBounds params jumpBounds regState)
        _ -> error ("Syscall could not interpret next PC: " ++ show (regState ^. curIP))
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


preserveRegAcrossSyscall :: ArchReg ARM.AArch32 tp -> Bool
preserveRegAcrossSyscall r =
    Some r `Set.member` linuxSystemCallPreservedRegisters
