{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.PPC.Eval (
  mkInitialAbsState,
  absEvalArchFn,
  absEvalArchStmt,
  postCallAbsState,
  postPPCTermStmtAbsState,
  preserveRegAcrossSyscall
  ) where

import           GHC.TypeLits

import           Control.Lens ( (&), (.~), (^.) )
import qualified Data.Set as S

import           Data.Macaw.AbsDomain.AbsState as MA
import           Data.Macaw.CFG
import qualified Data.Macaw.Memory as MM
import           Data.Parameterized.Some ( Some(..) )
import qualified SemMC.Architecture.PPC as SP

import qualified Dismantle.PPC as D

import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import qualified Data.Macaw.BinaryLoader as BL
import           Data.Macaw.PPC.Arch
import           Data.Macaw.PPC.PPCReg
import qualified Data.Macaw.BinaryLoader.PPC as BLP
import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC

preserveRegAcrossSyscall :: (ArchReg ppc ~ PPCReg ppc, 1 <= RegAddrWidth (PPCReg ppc))
                         => proxy ppc
                         -> ArchReg ppc tp
                         -> Bool
preserveRegAcrossSyscall proxy r = S.member (Some r) (linuxSystemCallPreservedRegisters proxy)

postPPCTermStmtAbsState :: (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
                        => (forall tp . PPCReg ppc tp -> Bool)
                        -> MM.Memory (RegAddrWidth (ArchReg ppc))
                        -> AbsBlockState (PPCReg ppc)
                        -> RegState (PPCReg ppc) (Value ppc ids)
                        -> PPCTermStmt ids
                        -> Maybe (MM.MemSegmentOff (RegAddrWidth (ArchReg ppc)), AbsBlockState (PPCReg ppc))
postPPCTermStmtAbsState preservePred mem s0 regState stmt =
  case stmt of
    PPCSyscall ->
      case simplifyValue (regState ^. curIP) of
        Just (RelocatableValue _ addr)
          | Just nextIP <- MM.asSegmentOff mem (MM.incAddr 4 addr) -> do
              let params = MA.CallParams { MA.postCallStackDelta = 0
                                         , MA.preserveReg = preservePred
                                         }
              Just (nextIP, MA.absEvalCall params s0 nextIP)
        _ -> error ("Syscall could not interpret next IP: " ++ show (regState ^. curIP))
    PPCTrap ->
      case simplifyValue (regState ^. curIP) of
        Just (RelocatableValue _ addr)
          | Just nextIP <- MM.asSegmentOff mem (MM.incAddr 4 addr) -> do
              let params = MA.CallParams { MA.postCallStackDelta = 0
                                         , MA.preserveReg = preservePred
                                         }
              Just (nextIP, MA.absEvalCall params s0 nextIP)
        _ -> error ("Syscall could not interpret next IP: " ++ show (regState ^. curIP))

-- | Set up an initial abstract state that holds at the beginning of a basic
-- block.
--
-- The 'MM.Memory' is the mapped memory region
--
-- The 'ArchSegmentOff' is the start address of the basic block.
--
-- Note that we don't initialize the abstract stack.  On PowerPC, there are no
-- initial stack entries (since the return address is in the link register).
--
-- One value that is definitely set is the link register, which holds the
-- abstract return value.
mkInitialAbsState :: ( ppc ~ SP.AnyPPC var
                     , PPCArchConstraints var
                     , BLP.HasTOC ppc binFmt
                     )
                  => proxy ppc
                  -> BL.LoadedBinary ppc binFmt
                  -> MM.Memory (RegAddrWidth (ArchReg ppc))
                  -> ArchSegmentOff ppc
                  -> MA.AbsBlockState (ArchReg ppc)
mkInitialAbsState _ binData _mem startAddr =
  case TOC.lookupTOCAbs (BLP.getTOC binData) startAddr of
    Just tocAddr -> s0 & MA.absRegState . boundValue (PPC_GP (D.GPR 2)) .~ tocAddr
    Nothing -> s0
  where
    s0 = MA.top & MA.setAbsIP startAddr
                & MA.absRegState . boundValue PPC_LNK .~ MA.ReturnAddr
                & MA.absRegState . boundValue (PPC_GP (D.GPR 1)) .~ MA.concreteStackOffset (segoffAddr startAddr) 0

absEvalArchFn :: (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
              => proxy ppc
              -> AbsProcessorState (ArchReg ppc) ids
              -> ArchFn ppc (Value ppc ids) tp
              -> AbsValue (RegAddrWidth (ArchReg ppc)) tp
absEvalArchFn _ _r = \case
  SDiv{}         -> MA.TopV
  UDiv{}         -> MA.TopV
  FPNeg{}        -> MA.TopV
  FPAbs{}        -> MA.TopV
  FPSqrt{}       -> MA.TopV
  FPAdd{}        -> MA.TopV
  FPSub{}        -> MA.TopV
  FPMul{}        -> MA.TopV
  FPDiv{}        -> MA.TopV
  FPFMA{}        -> MA.TopV
  FPLt{}         -> MA.TopV
  FPEq{}         -> MA.TopV
  FPLe{}         -> MA.TopV
  FPIsNaN{}      -> MA.TopV
  FPCast{}       -> MA.TopV
  FPRound{}      -> MA.TopV
  FPToBinary{}   -> MA.TopV
  FPFromBinary{} -> MA.TopV
  FPToSBV{}      -> MA.TopV
  FPToUBV{}      -> MA.TopV
  FPFromSBV{}    -> MA.TopV
  FPFromUBV{}    -> MA.TopV
  FPCoerce{}     -> MA.TopV
  FPSCR1{}       -> MA.TopV
  FPSCR2{}       -> MA.TopV
  FPSCR3{}       -> MA.TopV
  FP1{}          -> MA.TopV
  FP2{}          -> MA.TopV
  FP3{}          -> MA.TopV
  Vec1{}         -> MA.TopV
  Vec2{}         -> MA.TopV
  Vec3{}         -> MA.TopV

-- | For now, none of the architecture-specific statements have an effect on the
-- abstract value.
absEvalArchStmt :: proxy ppc
                -> AbsProcessorState (ArchReg ppc) ids
                -> ArchStmt ppc (Value ppc ids)
                -> AbsProcessorState (ArchReg ppc) ids
absEvalArchStmt _ s _ = s

-- | There should be no difference in stack height before and after a call, as
-- the callee pushes the return address if required.  Return values are also
-- passed in registers.
postCallAbsState :: (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
                 => proxy ppc
                 -> AbsBlockState (ArchReg ppc)
                 -> ArchSegmentOff ppc
                 -> AbsBlockState (ArchReg ppc)
postCallAbsState proxy = MA.absEvalCall params
  where
    params = MA.CallParams { MA.postCallStackDelta = 0
                           , MA.preserveReg = \r -> S.member (Some r) (linuxCalleeSaveRegisters proxy)
                           }
