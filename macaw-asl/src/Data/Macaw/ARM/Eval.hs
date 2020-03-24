{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
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
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Set as Set
import           GHC.TypeLits

callParams :: (ARMReg ~ ArchReg arm)
           => (forall tp . ARMReg tp -> Bool)
           -> MA.CallParams ARMReg
callParams preservePred =
  MA.CallParams { MA.postCallStackDelta = 0
                , MA.preserveReg = preservePred
                , MA.stackGrowsDown = True
                }

initialBlockRegs :: forall ids arm . ARMArchConstraints arm =>
                    ArchSegmentOff arm
                    -- ^ The address of the block
                 -> ArchBlockPrecond arm
                 -> RegState (ArchReg arm) (Value arm ids)
initialBlockRegs addr _preconds = MSG.initRegState addr

extractBlockPrecond :: (MI.ArchBlockPrecond arm ~ ())
                    => ArchSegmentOff arm
                    -> MA.AbsBlockState (ArchReg arm)
                    -> Either String (MI.ArchBlockPrecond arm)
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
mkInitialAbsState :: (ARMArchConstraints arm, ArchStmt arm ~ ARMStmt)
                  => proxy arm
                  -> MM.Memory (RegAddrWidth (ArchReg arm))
                  -> ArchSegmentOff arm
                  -> MA.AbsBlockState (ArchReg arm)
mkInitialAbsState _ _mem startAddr =
  s0 & MA.absRegState . boundValue arm_LR .~ MA.ReturnAddr
  -- FIXME: Initialize every single global to macaw's "Initial" value
  where initRegVals = MapF.fromList []
        s0 = MA.fnStartAbsBlockState startAddr initRegVals []


absEvalArchFn :: (ARMArchConstraints arm)
              => proxy arm
              -> AbsProcessorState (ArchReg arm) ids
              -> ArchFn arm (Value arm ids) tp
              -> AbsValue (RegAddrWidth (ArchReg arm)) tp
absEvalArchFn _ _r f =
  case f of
    UDiv{} -> MA.TopV
    SDiv{} -> MA.TopV
    URem{} -> MA.TopV
    SRem{} -> MA.TopV

-- For now, none of the architecture-specific statements have an effect on the
-- abstract value.
absEvalArchStmt :: proxy arch
                -> AbsProcessorState (ArchReg arch) ids
                -> ArchStmt arch (Value arch ids)
                -> AbsProcessorState (ArchReg arch) ids
absEvalArchStmt _ s _ = s


postARMTermStmtAbsState :: (ARMArchConstraints arm)
                        => (forall tp . ARMReg tp -> Bool)
                        -> MM.Memory (RegAddrWidth (ArchReg arm))
                        -> AbsProcessorState ARMReg ids
                        -> MJ.IntraJumpBounds arm ids
                        -> RegState ARMReg (Value arm ids)
                        -> ARMTermStmt ids
                        -> Maybe (MM.MemSegmentOff (RegAddrWidth (ArchReg arm)), AbsBlockState ARMReg, MJ.InitJumpBounds arm)
postARMTermStmtAbsState preservePred mem s0 jumpBounds regState stmt =
  case stmt of
    ARMTermStmt -> error "no implementation for ARMTermStmt"
    -- FIXME: Check semantics for SVC. Is there a special function
    -- that we need to translate?
    
    -- ARMSyscall _ ->
    --   case simplifyValue (regState^.curIP) of
    --     Just (RelocatableValue _ addr)
    --       | Just nextPC <- MM.asSegmentOff mem (MM.incAddr 4 addr) -> do
    --           let params = MA.CallParams { MA.postCallStackDelta = 0
    --                                      , MA.preserveReg = preservePred
    --                                      }
    --           Just (nextPC, MA.absEvalCall params s0 regState nextPC)
    --     _ -> error ("Syscall could not interpret next PC: " ++ show (regState ^. curIP))
    -- ThumbSyscall _ ->
    --   case simplifyValue (regState^.curIP) of
    --     Just (RelocatableValue _ addr)
    --       | Just nextPC <- MM.asSegmentOff mem (MM.incAddr 2 addr) -> do
    --           let params = MA.CallParams { MA.postCallStackDelta = 0
    --                                      , MA.preserveReg = preservePred
    --                                      }
    --           Just (nextPC, MA.absEvalCall params s0 regState nextPC)
    --     _ -> error ("Syscall could not interpret next PC: " ++ show (regState ^. curIP))


preserveRegAcrossSyscall :: (ArchReg arm ~ ARMReg, 1 <= RegAddrWidth ARMReg)
                         => proxy arm
                         -> ArchReg arm tp
                         -> Bool
preserveRegAcrossSyscall proxy r =
    Some r `Set.member` (linuxSystemCallPreservedRegisters proxy)
