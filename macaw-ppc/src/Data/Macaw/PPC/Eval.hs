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
import qualified Data.Macaw.Architecture.Info as MI
import           Data.Macaw.CFG
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified SemMC.Architecture.PPC as SP
import           Text.PrettyPrint.ANSI.Leijen ( pretty )

import qualified Dismantle.PPC as D

import qualified Data.Macaw.SemMC.Generator as MSG
import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import qualified Data.Macaw.BinaryLoader as BL
import           Data.Macaw.PPC.Arch
import           Data.Macaw.PPC.PPCReg
import qualified Data.Macaw.BinaryLoader.PPC as BLP
import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC

ppcCallParams :: (PPCReg ppc ~ ArchReg ppc) => (forall tp . PPCReg ppc tp -> Bool) -> MA.CallParams (PPCReg ppc)
ppcCallParams preservePred =
  MA.CallParams { MA.postCallStackDelta = 0
                , MA.preserveReg = preservePred
                , MA.stackGrowsDown = True
                }

ppcInitialBlockRegs :: (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
                    => ArchSegmentOff ppc
                    -> MI.ArchBlockPrecond ppc
                    -> RegState (PPCReg ppc) (Value ppc ids)
ppcInitialBlockRegs addr _preconds = MSG.initRegState addr

ppcExtractBlockPrecond :: (MI.ArchBlockPrecond ppc ~ ())
                       => ArchSegmentOff ppc
                       -> MA.AbsBlockState (ArchReg ppc)
                       -> Either String (MI.ArchBlockPrecond ppc)
ppcExtractBlockPrecond _ _ = Right ()

preserveRegAcrossSyscall :: (ArchReg ppc ~ PPCReg ppc, 1 <= RegAddrWidth (PPCReg ppc))
                         => proxy ppc
                         -> ArchReg ppc tp
                         -> Bool
preserveRegAcrossSyscall proxy r = S.member (Some r) (linuxSystemCallPreservedRegisters proxy)

postPPCTermStmtAbsState :: forall var ppc ids
                         . (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
                        => (forall tp . PPCReg ppc tp -> Bool)
                        -> MM.Memory (RegAddrWidth (ArchReg ppc))
                        -> AbsProcessorState (PPCReg ppc) ids
                        -> MJ.IntraJumpBounds ppc ids
                        -> RegState (PPCReg ppc) (Value ppc ids)
                        -> PPCTermStmt ppc ids
                        -> Maybe (MM.MemSegmentOff (RegAddrWidth (ArchReg ppc)), AbsBlockState (PPCReg ppc), MJ.InitJumpBounds ppc)
postPPCTermStmtAbsState preservePred mem s0 jumpBounds regState stmt =
  case stmt of
    PPCSyscall ->
      case simplifyValue (regState ^. curIP) of
        Just (RelocatableValue _ addr)
          | Just nextIP <- MM.asSegmentOff mem (MM.incAddr 4 addr) ->
              Just (nextIP, MA.absEvalCall params s0 regState nextIP, MJ.postCallBounds params jumpBounds regState)
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
    initRegVals = MapF.fromList [ MapF.Pair PPC_LNK MA.ReturnAddr ]
    s0 = MA.fnStartAbsBlockState startAddr initRegVals []

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
