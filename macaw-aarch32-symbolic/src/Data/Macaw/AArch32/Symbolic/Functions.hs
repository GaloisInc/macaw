{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Macaw.AArch32.Symbolic.Functions (
  SymFuns
  , newSymFuns
  , funcSemantics
  , stmtSemantics
  , termSemantics
  -- * Exceptions
  , AArch32Exception(..)
  ) where

import qualified Control.Exception as X
import           Control.Lens ( (^.) )
import qualified Data.IORef as IOR
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import           Text.Printf ( printf )

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.MemModel as LL
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.ExecutionTree as CSET
import qualified Lang.Crucible.Types as CT
import qualified What4.BaseTypes as WT
import qualified What4.Interface as WI
import qualified What4.Symbol as WS

import qualified Data.Macaw.AArch32.Symbolic.AtomWrapper as AA
import qualified Data.Macaw.AArch32.Symbolic.Panic as AP
import qualified Data.Macaw.ARM.Arch as MAA
import qualified Dismantle.ARM.A32 as ARMDis
import qualified Dismantle.ARM.T32 as ThumbDis
import qualified SemMC.Architecture.AArch32 as SA

data SomeSymFun sym where
  SomeSymFun :: Ctx.Assignment WT.BaseTypeRepr ps -> WT.BaseTypeRepr r -> WI.SymFn sym ps r -> SomeSymFun sym

data SymFuns sym =
  SymFuns { symFuns :: IOR.IORef (Map.Map String (SomeSymFun sym))
          }

data AArch32Exception where
  MissingSemanticsForA32Instruction :: ARMDis.Opcode ARMDis.Operand s -> AArch32Exception
  MissingSemanticsForT32Instruction :: ThumbDis.Opcode ThumbDis.Operand s -> AArch32Exception
  MissingSemanticsForFunction :: String -> AArch32Exception
  UnsupportedSyscall :: AArch32Exception

deriving instance Show AArch32Exception
instance X.Exception AArch32Exception

newSymFuns :: (CB.IsSymInterface sym) => sym -> IO (SymFuns sym)
newSymFuns _sym = do
  r <- IOR.newIORef Map.empty
  return SymFuns { symFuns = r }

type S p sym rtp bs r ctx = CS.CrucibleState p sym (MS.MacawExt SA.AArch32) rtp bs r ctx

-- | Semantics for ARM-specific block terminators
--
-- Right now we only have one: system call.  This will eventually need to
-- inspect the current register state in order to determine what system call was
-- issued under the ABI.
--
-- It is not currently clear where that information might come from (it is
-- implicitly in 'S', but might be hard to dig out).  It would probably be
-- easier to just include the necessary register snapshot in the terminator (and
-- traverse them appropriately to translate into Crucible terms)
termSemantics :: (CB.IsSymInterface sym)
              => SymFuns sym
              -> MAA.ARMTermStmt ids
              -> S p sym rtp bs r ctx
              -> IO (CS.RegValue sym CT.UnitType, S p sym rtp bs r ctx)
termSemantics _sfns tstmt _st0 =
  case tstmt of
    MAA.ARMSyscall _payload ->
      X.throwIO UnsupportedSyscall
    MAA.ThumbSyscall _payload ->
      X.throwIO UnsupportedSyscall

-- | Semantics for statement syntax extensions
--
-- Right now, there is only one statement, which represents instructions for which we lack semantics.
-- All we can do for this is stop symbolic execution and report that to the caller (so that semantics
-- can be added).
stmtSemantics :: (CB.IsSymInterface sym)
              => SymFuns sym
              -> MAA.ARMStmt (AA.AtomWrapper (CS.RegEntry sym))
              -> S p sym rtp bs r ctx
              -> IO (CS.RegValue sym CT.UnitType, S p sym rtp bs r ctx)
stmtSemantics _sfns stmt _st0 =
  case stmt of
    MAA.UninterpretedA32Opcode opc _ops ->
      X.throwIO (MissingSemanticsForA32Instruction opc)
    MAA.UninterpretedT32Opcode opc _ops ->
      X.throwIO (MissingSemanticsForT32Instruction opc)

funcSemantics :: (CB.IsSymInterface sym, MS.ToCrucibleType mt ~ t)
              => SymFuns sym
              -> MAA.ARMPrimFn (AA.AtomWrapper (CS.RegEntry sym)) mt
              -> S p sym rtp bs r ctx
              -> IO (CS.RegValue sym t, S p sym rtp bs r ctx)
funcSemantics sfns fn st0 =
  case fn of
    MAA.SDiv _rep lhs rhs -> withSym st0 $ \sym -> do
      lhs' <- toValBV sym lhs
      rhs' <- toValBV sym rhs
      -- NOTE: We are applying division directly here without checking the divisor for zero.
      --
      -- The ARM semantics explicitly check this and have different behaviors
      -- depending on what CPU flags are set; this operation is never called
      -- with a divisor of zero.  We could add an assertion to that effect here,
      -- but it might be difficult to prove.
      LL.llvmPointer_bv sym =<< WI.bvSdiv sym lhs' rhs'
    MAA.UDiv _rep lhs rhs -> withSym st0 $ \sym -> do
      lhs' <- toValBV sym lhs
      rhs' <- toValBV sym rhs
      -- NOTE: See the note in SDiv
      LL.llvmPointer_bv sym =<< WI.bvUdiv sym lhs' rhs'
    MAA.URem _rep lhs rhs -> withSym st0 $ \sym -> do
      lhs' <- toValBV sym lhs
      rhs' <- toValBV sym rhs
      -- NOTE: See the note in SDiv
      LL.llvmPointer_bv sym =<< WI.bvUrem sym lhs' rhs'
    MAA.SRem _rep lhs rhs -> withSym st0 $ \sym -> do
      lhs' <- toValBV sym lhs
      rhs' <- toValBV sym rhs
      -- NOTE: See the note in SDiv
      LL.llvmPointer_bv sym =<< WI.bvSrem sym lhs' rhs'
    MAA.UnsignedRSqrtEstimate _rep v -> withSym st0 $ \sym -> do
      v' <- toValBV sym v
      let args = Ctx.empty Ctx.:> v'
      res <- lookupApplySymFun sym sfns "unsignedRSqrtEstimate" CT.knownRepr args CT.knownRepr
      LL.llvmPointer_bv sym res
    MAA.FPSub {} -> X.throwIO (MissingSemanticsForFunction "FPSub")
    MAA.FPAdd {} -> X.throwIO (MissingSemanticsForFunction "FPAdd")
    MAA.FPMul {} -> X.throwIO (MissingSemanticsForFunction "FPMul")
    MAA.FPDiv {} -> X.throwIO (MissingSemanticsForFunction "FPDiv")
    MAA.FPRecipEstimate {} -> X.throwIO (MissingSemanticsForFunction "FPRecipEstimate")
    MAA.FPRecipStep {} -> X.throwIO (MissingSemanticsForFunction "FPRecipStep")
    MAA.FPSqrtEstimate {} -> X.throwIO (MissingSemanticsForFunction "FPSqrtEstimate")
    MAA.FPRSqrtStep {} -> X.throwIO (MissingSemanticsForFunction "FPRSqrtStep")
    MAA.FPSqrt {} -> X.throwIO (MissingSemanticsForFunction "FPSqrt")
    MAA.FPMax {} -> X.throwIO (MissingSemanticsForFunction "FPMax")
    MAA.FPMin {} -> X.throwIO (MissingSemanticsForFunction "FPMin")
    MAA.FPMaxNum {} -> X.throwIO (MissingSemanticsForFunction "FPMaxNum")
    MAA.FPMinNum {} -> X.throwIO (MissingSemanticsForFunction "FPMinNum")
    MAA.FPMulAdd {} -> X.throwIO (MissingSemanticsForFunction "FPMulAdd")
    MAA.FPCompareGE {} -> X.throwIO (MissingSemanticsForFunction "FPCompareGE")
    MAA.FPCompareGT {} -> X.throwIO (MissingSemanticsForFunction "FPCompareGT")
    MAA.FPCompareEQ {} -> X.throwIO (MissingSemanticsForFunction "FPCompareEQ")
    MAA.FPCompareNE {} -> X.throwIO (MissingSemanticsForFunction "FPCompareNE")
    MAA.FPCompareUN {} -> X.throwIO (MissingSemanticsForFunction "FPCompareUN")
    MAA.FPToFixed {} -> X.throwIO (MissingSemanticsForFunction "FPToFixed")
    MAA.FixedToFP {} -> X.throwIO (MissingSemanticsForFunction "FixedToFP")
    MAA.FPConvert {} -> X.throwIO (MissingSemanticsForFunction "FPConvert")
    MAA.FPToFixedJS {} -> X.throwIO (MissingSemanticsForFunction "FPToFixedJS")
    MAA.FPRoundInt {} -> X.throwIO (MissingSemanticsForFunction "FPRoundInt")

withSym :: (CB.IsSymInterface sym)
        => S p sym rtp bs r ctx
        -> (sym -> IO a)
        -> IO (a, S p sym rtp bs r ctx)
withSym s action = do
  let sym = s ^. CSET.stateSymInterface
  val <- action sym
  return (val, s)


-- | Assert that the wrapped value is a bitvector
toValBV :: (CB.IsSymInterface sym)
        => sym
        -> AA.AtomWrapper (CS.RegEntry sym) (MT.BVType w)
        -> IO (CS.RegValue sym (CT.BVType w))
toValBV sym (AA.AtomWrapper x) = LL.projectLLVM_bv sym (CS.regValue x)

-- | Apply an uninterpreted function to the provided arguments
--
-- If there is already a function allocated with that name, re-use it.
-- Otherwise, allocate a fresh function and store it in a persistent mapping
-- (inside of an IORef)
lookupApplySymFun :: (CB.IsSymInterface sym)
                  => sym
                  -> SymFuns sym
                  -> String
                  -> Ctx.Assignment WT.BaseTypeRepr ps
                  -> Ctx.Assignment (WI.SymExpr sym) ps
                  -> WT.BaseTypeRepr r
                  -> IO (WI.SymExpr sym r)
lookupApplySymFun sym sf name argReprs args retRepr = do
  r <- IOR.readIORef (symFuns sf)
  case Map.lookup name r of
    Just (SomeSymFun argReprs' retRepr' fn)
      | Just PC.Refl <- PC.testEquality argReprs' argReprs
      , Just PC.Refl <- PC.testEquality retRepr' retRepr ->
        WI.applySymFn sym fn args
      | otherwise ->
        AP.panic AP.AArch32 "lookupApplySymFun" [printf "Invalid type for symbolic function '%s' expected %s but got %s " name (show (argReprs, retRepr)) (show (argReprs', retRepr'))]
    Nothing -> do
      fn <- WI.freshTotalUninterpFn sym (WS.safeSymbol name) argReprs retRepr
      IOR.modifyIORef (symFuns sf) (Map.insert name (SomeSymFun argReprs retRepr fn))
      WI.applySymFn sym fn args
