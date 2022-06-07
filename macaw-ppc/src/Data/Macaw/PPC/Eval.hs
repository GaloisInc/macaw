{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Macaw.PPC.Eval (
  mkInitialAbsState,
  absEvalArchFn,
  absEvalArchStmt,
  ppcInitialBlockRegs,
  ppcCallParams,
  ppcExtractBlockPrecond,
  postPPCTermStmtAbsState,
  preserveRegAcrossSyscall
  ) where

import           GHC.TypeLits

import           Control.Lens ( (&), (.~), (^.) )
import qualified Data.Set as S

import           Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.AbsDomain.JumpBounds as MJ
import           Data.Macaw.CFG
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified SemMC.Architecture.PPC as SP
import           Prettyprinter ( pretty )

import qualified Dismantle.PPC as D

import qualified Data.Macaw.SemMC.Generator as MSG
import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Macaw.PPC.Arch
import           Data.Macaw.PPC.PPCReg
import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC

ppcCallParams :: (forall tp . PPCReg v tp -> Bool) -> MA.CallParams (PPCReg v)
ppcCallParams preservePred =
  MA.CallParams { MA.postCallStackDelta = 0
                , MA.preserveReg = preservePred
                , MA.stackGrowsDown = True
                }

ppcInitialBlockRegs :: (PPCArchConstraints v)
                    => ArchSegmentOff (SP.AnyPPC v)
                    -> ArchBlockPrecond (SP.AnyPPC v)
                    -> RegState (PPCReg v) (Value (SP.AnyPPC v) ids)
ppcInitialBlockRegs addr _preconds = MSG.initRegState addr

ppcExtractBlockPrecond :: ArchSegmentOff (SP.AnyPPC v)
                       -> MA.AbsBlockState (PPCReg v)
                       -> Either String (ArchBlockPrecond (SP.AnyPPC v))
ppcExtractBlockPrecond _ _ = Right ()

preserveRegAcrossSyscall :: (1 <= RegAddrWidth (PPCReg v))
                         => proxy v
                         -> PPCReg v tp
                         -> Bool
preserveRegAcrossSyscall proxy r = S.member (Some r) (linuxSystemCallPreservedRegisters proxy)

postPPCTermStmtAbsState :: forall var ids
                         . (PPCArchConstraints var)
                        => (forall tp . PPCReg var tp -> Bool)
                        -> MM.Memory (SP.AddrWidth var)
                        -> AbsProcessorState (PPCReg var) ids
                        -> MJ.IntraJumpBounds (SP.AnyPPC var) ids
                        -> RegState (PPCReg var) (Value (SP.AnyPPC var) ids)
                        -> PPCTermStmt var (Value (SP.AnyPPC var) ids)
                        -> Maybe (MM.MemSegmentOff (SP.AddrWidth var), AbsBlockState (PPCReg var), MJ.InitJumpBounds (SP.AnyPPC var))
postPPCTermStmtAbsState preservePred mem s0 jumpBounds regState stmt =
  case stmt of
    PPCSyscall ->
      -- We treat syscalls as closely to a no-op as we can. The call transfer
      -- function ('MA.absEvalCall') is a bit too aggressive and breaks the
      -- abstract value propagation for the link register, which prevents
      -- returns from being recognized.
      --
      -- This version just calls the standard abstract transfer function on
      -- every register, which is safe.
      --
      -- Note that this complexity will be reduced when we change system calls
      -- to be statements instead of terminators.
      case simplifyValue (regState ^. curIP) of
        Just (RelocatableValue _ addr)
          | Just nextIP <- MM.asSegmentOff mem (MM.incAddr 4 addr) ->
              Just (nextIP, MA.finalAbsBlockState s0 regState, MJ.postCallBounds params jumpBounds regState)
        _ -> error ("Syscall could not interpret next IP: " ++ show (pretty $ regState ^. curIP))
    PPCTrap ->
      case simplifyValue (regState ^. curIP) of
        Just (RelocatableValue _ addr)
          | Just nextIP <- MM.asSegmentOff mem (MM.incAddr 4 addr) ->
              Just (nextIP, MA.absEvalCall params s0 regState nextIP, MJ.postCallBounds params jumpBounds regState)
        _ -> error ("Syscall could not interpret next IP: " ++ show (pretty $ regState ^. curIP))
    PPCTrapdword _ _ _ ->
      case simplifyValue (regState ^. curIP) of
        Just (RelocatableValue _ addr)
          | Just nextIP <- MM.asSegmentOff mem (MM.incAddr 4 addr) ->
              Just (nextIP, MA.absEvalCall params s0 regState nextIP, MJ.postCallBounds params jumpBounds regState)
        _ -> error ("Syscall could not interpret next IP: " ++ show (pretty $ regState ^. curIP))
  where
    params = ppcCallParams preservePred

-- | Set up an initial abstract state that holds at the beginning of a basic
-- block.
--
-- The 'MM.Memory' is the mapped memory region
--
-- The 'ArchSegmentOff' is the start address of the basic block.
--
-- Note that we don't explicitly initialize the abstract stack.  On PowerPC, there are no
-- initial stack entries (since the return address is in the link register).
--
-- One value that is definitely set is the link register, which holds the
-- abstract return value.  When available, we also populate the abstract state
-- with the Table of Contents pointer (in r2).
mkInitialAbsState :: ( PPCArchConstraints var
                     )
                  => proxy var
                  -> Maybe (TOC.TOC (SP.AddrWidth var))
                  -> MM.Memory (SP.AddrWidth var)
                  -> ArchSegmentOff (SP.AnyPPC var)
                  -> MA.AbsBlockState (PPCReg var)
mkInitialAbsState _ mtoc _mem startAddr =
  case mtoc of
    Just toc
      | Just tocAddr <- TOC.lookupTOCAbs toc startAddr ->
        s0 & MA.absRegState . boundValue (PPC_GP (D.GPR 2)) .~ tocAddr
    _ -> s0
  where
    initRegVals = MapF.fromList [ MapF.Pair PPC_LNK MA.ReturnAddr ]
    s0 = MA.fnStartAbsBlockState startAddr initRegVals []

absEvalArchFn :: (PPCArchConstraints var)
              => proxy var
              -> AbsProcessorState (PPCReg var) ids
              -> PPCPrimFn var (Value (SP.AnyPPC var) ids) tp
              -> AbsValue (SP.AddrWidth var) tp
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
absEvalArchStmt :: proxy v
                -> AbsProcessorState (PPCReg v) ids
                -> PPCStmt v (Value (SP.AnyPPC v) ids)
                -> AbsProcessorState (PPCReg v) ids
absEvalArchStmt _ s _ = s
