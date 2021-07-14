{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.PPC.Symbolic.Functions (
  SymFuns,
  newSymFuns,
  funcSemantics,
  stmtSemantics,
  termSemantics,
  -- * Exceptions
  SemanticsError(..)
  ) where

import           GHC.TypeLits

import qualified Control.Exception as X
import           Control.Lens ( (^.) )
import qualified Data.IORef as IO
import qualified Data.Map.Strict as M
import           Data.Parameterized.Classes ( (:~:)( Refl ), testEquality )
import qualified Data.Parameterized.Context as Ctx
import           Text.Printf ( printf )

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.LLVM.MemModel as LL
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C
import qualified Lang.Crucible.Types as C
import qualified What4.Interface as C
import qualified What4.InterpretedFloatingPoint as C

import qualified SemMC.Architecture.PPC as SP
import qualified SemMC.Util as U
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.PPC as MP

import qualified Data.Macaw.PPC.Symbolic.AtomWrapper as A

data SomeSymFun sym where
  SomeSymFun :: Ctx.Assignment C.BaseTypeRepr ps -> C.BaseTypeRepr r -> C.SymFn sym ps r -> SomeSymFun sym

data SymFuns sym =
  SymFuns { symFuns :: IO.IORef (M.Map String (SomeSymFun sym))
          }

newSymFuns :: forall sym . (C.IsSymInterface sym) => sym -> IO (SymFuns sym)
newSymFuns _sym = do
  r <- IO.newIORef M.empty
  return SymFuns { symFuns = r
                 }

data SemanticsError = NonUserSymbol String
  deriving (Show)

instance X.Exception SemanticsError

termSemantics :: (C.IsSymInterface sym, 1 <= SP.AddrWidth v)
              => SymFuns sym
              -> MP.PPCTermStmt v ids
              -> S p v sym rtp bs r ctx
              -> IO (C.RegValue sym C.UnitType, S p v sym rtp bs r ctx)
termSemantics = error "PowerPC-specific terminator statement semantics not yet implemented"

stmtSemantics :: (C.IsSymInterface sym, 1 <= SP.AddrWidth v)
              => SymFuns sym
              -> MP.PPCStmt v (A.AtomWrapper (C.RegEntry sym))
              -> S p v sym rtp bs r ctx
              -> IO (C.RegValue sym C.UnitType, S p v sym rtp bs r ctx)
stmtSemantics _sf stmt s =
  case stmt of
    MP.Attn -> do
      let reason = C.GenericSimError "ppc_attn"
      C.addFailedAssertion (s ^. C.stateSymInterface) reason
    -- These are cache hints that can't be observed in our current memory model
    -- (i.e., they require concurrency to be observed).
    --
    -- Some take memory addresses as arguments.  We don't actually touch those
    -- addresses here, as they might not be valid (the instructions don't fault
    -- on invalid addresses).
    MP.Sync -> return ((), s)
    MP.Isync -> return ((), s)
    MP.Dcba {} -> return ((), s)
    MP.Dcbf {} -> return ((), s)
    MP.Dcbi {} -> return ((), s)
    MP.Dcbst {} -> return ((), s)
    MP.Dcbz {} -> return ((), s)
    MP.Dcbzl {} -> return ((), s)
    MP.Dcbt {} -> return ((), s)
    MP.Dcbtst {} -> return ((), s)
    MP.Icbi {} -> return ((), s)
    MP.Icbt {} -> return ((), s)
    -- These are transactional memory instructions.  These also can't really
    -- fail without concurrency, so we don't have them do anything.  FIXME: That
    -- might not be entirely correct - there could be some interesting side
    -- effects that need to be captured somehow.  We could, for example, model
    -- Tcheck as both failing and succeeding to explore both paths.
    MP.Tabort {} -> return ((), s)
    MP.Tabortdc {} -> return ((), s)
    MP.Tabortdci {} -> return ((), s)
    MP.Tabortwc {} -> return ((), s)
    MP.Tabortwci {} -> return ((), s)
    MP.Tbegin {} -> return ((), s)
    MP.Tcheck {} -> return ((), s)
    MP.Tend {} -> return ((), s)

funcSemantics :: (C.IsSymInterface sym, MS.ToCrucibleType mt ~ t, 1 <= SP.AddrWidth v)
              => SymFuns sym
              -> MP.PPCPrimFn v (A.AtomWrapper (C.RegEntry sym)) mt
              -> S p v sym rtp bs r ctx
              -> IO (C.RegValue sym t, S p v sym rtp bs r ctx)
funcSemantics sf pf s =
  case pf of
    MP.UDiv _rep lhs rhs -> do
      let sym = s ^. C.stateSymInterface
      lhs' <- toValBV sym lhs
      rhs' <- toValBV sym rhs
      -- FIXME: Make sure that the semantics when rhs == 0 exactly match PowerPC.
      v <- LL.llvmPointer_bv sym =<< C.bvUdiv sym lhs' rhs'
      return (v, s)
    MP.SDiv _rep lhs rhs -> do
      let sym = s ^. C.stateSymInterface
      lhs' <- toValBV sym lhs
      rhs' <- toValBV sym rhs
      -- FIXME: Make sure that the semantics when rhs == 0 exactly match PowerPC.
      v <- LL.llvmPointer_bv sym =<< C.bvSdiv sym lhs' rhs'
      return (v, s)
    MP.FPNeg (_ :: MT.FloatInfoRepr fi) x -> withSymFPUnOp s x $ \sym x' ->
      C.iFloatNeg @_ @(MS.ToCrucibleFloatInfo fi) sym x'
    MP.FPAbs (_ :: MT.FloatInfoRepr fi) x -> withSymFPUnOp s x $ \sym x' ->
      C.iFloatAbs @_ @(MS.ToCrucibleFloatInfo fi) sym x'
    MP.FPSqrt (_ :: MT.FloatInfoRepr fi) r x ->
      withSymFPUnOp s x $ \sym x' -> withRounding sym r $ \rm ->
        C.iFloatSqrt @_ @(MS.ToCrucibleFloatInfo fi) sym rm x'
    MP.FPAdd (_ :: MT.FloatInfoRepr fi) r x y ->
      withSymFPBinOp s x y $ \sym x' y' -> withRounding sym r $ \rm ->
        C.iFloatAdd @_ @(MS.ToCrucibleFloatInfo fi) sym rm x' y'
    MP.FPSub (_ :: MT.FloatInfoRepr fi) r x y ->
      withSymFPBinOp s x y $ \sym x' y' -> withRounding sym r $ \rm ->
        C.iFloatSub @_ @(MS.ToCrucibleFloatInfo fi) sym rm x' y'
    MP.FPMul (_ :: MT.FloatInfoRepr fi) r x y ->
      withSymFPBinOp s x y $ \sym x' y' -> withRounding sym r $ \rm ->
        C.iFloatMul @_ @(MS.ToCrucibleFloatInfo fi) sym rm x' y'
    MP.FPDiv (_ :: MT.FloatInfoRepr fi) r x y ->
      withSymFPBinOp s x y $ \sym x' y' -> withRounding sym r $ \rm ->
        C.iFloatDiv @_ @(MS.ToCrucibleFloatInfo fi) sym rm x' y'
    MP.FPFMA (_ :: MT.FloatInfoRepr fi) r x y z ->
      withSym s $ \sym -> withRounding sym r $ \rm -> do
        let x' = toValFloat sym x
        let y' = toValFloat sym y
        let z' = toValFloat sym z
        C.iFloatFMA @_ @(MS.ToCrucibleFloatInfo fi) sym rm x' y' z'
    MP.FPLt (x :: A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)) y ->
      withSymFPBinOp s x y $ \sym x' y' ->
        C.iFloatLt @_ @(MS.ToCrucibleFloatInfo fi) sym x' y'
    MP.FPEq (x :: A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)) y ->
      withSymFPBinOp s x y $ \sym x' y' ->
        C.iFloatFpEq @_ @(MS.ToCrucibleFloatInfo fi) sym x' y'
    MP.FPLe (x :: A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)) y ->
      withSymFPBinOp s x y $ \sym x' y' ->
        C.iFloatLe @_ @(MS.ToCrucibleFloatInfo fi) sym x' y'
    MP.FPIsNaN (x :: A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)) ->
      withSymFPUnOp s x $ \sym x' ->
        C.iFloatIsNaN @_ @(MS.ToCrucibleFloatInfo fi) sym x'
    MP.FPCast fi r (x :: A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi')) ->
      withSymFPUnOp s x $ \sym x' -> withRounding sym r $ \rm ->
        C.iFloatCast @_ @_ @(MS.ToCrucibleFloatInfo fi')
          sym
          (MS.floatInfoToCrucible fi)
          rm
          x'
    MP.FPRound (_ :: MT.FloatInfoRepr fi) r x ->
      withSymFPUnOp s x $ \sym x' -> withRounding sym r $ \rm ->
        C.iFloatRound @_ @(MS.ToCrucibleFloatInfo fi) sym rm x'
    MP.FPToBinary fi x -> withSymFPUnOp s x $ \sym x' -> case fi of
      MT.HalfFloatRepr ->
        LL.llvmPointer_bv sym
          =<< C.iFloatToBinary sym (MS.floatInfoToCrucible fi) x'
      MT.SingleFloatRepr ->
        LL.llvmPointer_bv sym
          =<< C.iFloatToBinary sym (MS.floatInfoToCrucible fi) x'
      MT.DoubleFloatRepr ->
        LL.llvmPointer_bv sym
          =<< C.iFloatToBinary sym (MS.floatInfoToCrucible fi) x'
      MT.QuadFloatRepr ->
        LL.llvmPointer_bv sym
          =<< C.iFloatToBinary sym (MS.floatInfoToCrucible fi) x'
      MT.X86_80FloatRepr ->
        LL.llvmPointer_bv sym
          =<< C.iFloatToBinary sym (MS.floatInfoToCrucible fi) x'
    MP.FPFromBinary fi x -> withSymBVUnOp s x $ \sym x' -> case fi of
      MT.HalfFloatRepr ->
        C.iFloatFromBinary sym (MS.floatInfoToCrucible fi) x'
      MT.SingleFloatRepr ->
        C.iFloatFromBinary sym (MS.floatInfoToCrucible fi) x'
      MT.DoubleFloatRepr ->
        C.iFloatFromBinary sym (MS.floatInfoToCrucible fi) x'
      MT.QuadFloatRepr ->
        C.iFloatFromBinary sym (MS.floatInfoToCrucible fi) x'
      MT.X86_80FloatRepr ->
        C.iFloatFromBinary sym (MS.floatInfoToCrucible fi) x'
    MP.FPToSBV w r (x :: A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)) ->
      withSymFPUnOp s x $ \sym x' -> do
        bv_val <- withRounding sym r $ \rm ->
          C.iFloatToSBV @_ @_ @(MS.ToCrucibleFloatInfo fi) sym w rm x'
        LL.llvmPointer_bv sym bv_val
    MP.FPToUBV w r (x :: A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)) ->
      withSymFPUnOp s x $ \sym x' -> do
        bv_val <- withRounding sym r $ \rm ->
          C.iFloatToBV @_ @_ @(MS.ToCrucibleFloatInfo fi) sym w rm x'
        LL.llvmPointer_bv sym bv_val
    MP.FPFromSBV fi r x ->
      withSymBVUnOp s x $ \sym x' -> withRounding sym r $ \rm ->
        C.iSBVToFloat sym (MS.floatInfoToCrucible fi) rm x'
    MP.FPFromUBV fi r x ->
      withSymBVUnOp s x $ \sym x' -> withRounding sym r $ \rm ->
        C.iBVToFloat sym (MS.floatInfoToCrucible fi) rm x'
    MP.FPCoerce (fi :: MT.FloatInfoRepr fi) (fi' :: MT.FloatInfoRepr fi') x ->
      withSymFPUnOp s x $ \sym x' -> do
        res <- C.iFloatCast @_ @_ @(MS.ToCrucibleFloatInfo fi')
          sym
          (MS.floatInfoToCrucible fi)
          C.RNE
          x'
        cond <- C.iFloatEq @_ @(MS.ToCrucibleFloatInfo fi') sym x'
          =<< C.iFloatCast @_ @_ @(MS.ToCrucibleFloatInfo fi)
                sym
                (MS.floatInfoToCrucible fi')
                C.RNE
                res
        C.assert sym cond $ C.GenericSimError $
          "float precision loss: coercing from "
          ++ show (MS.floatInfoToCrucible fi')
          ++ " to "
          ++ show (MS.floatInfoToCrucible fi)
        return res
    MP.FPSCR1 name x fpscr -> withSym s $ \sym -> do
      x' <- toValBV sym x
      fpscr' <- toValBV sym fpscr
      LL.llvmPointer_bv sym =<< lookupApplySymFun sym sf ("fpscr_" ++ name)
        C.knownRepr
        (Ctx.empty Ctx.:> x' Ctx.:> fpscr')
        C.knownRepr
    MP.FPSCR2 name x y fpscr -> withSym s $ \sym -> do
      x' <- toValBV sym x
      y' <- toValBV sym y
      fpscr' <- toValBV sym fpscr
      LL.llvmPointer_bv sym =<< lookupApplySymFun sym sf ("fpscr_" ++ name)
        C.knownRepr
        (Ctx.empty Ctx.:> x' Ctx.:> y' Ctx.:> fpscr')
        C.knownRepr
    MP.FPSCR3 name x y z fpscr -> withSym s $ \sym -> do
      x' <- toValBV sym x
      y' <- toValBV sym y
      z' <- toValBV sym z
      fpscr' <- toValBV sym fpscr
      LL.llvmPointer_bv sym =<< lookupApplySymFun sym sf ("fpscr_" ++ name)
        C.knownRepr
        (Ctx.empty Ctx.:> x' Ctx.:> y' Ctx.:> z' Ctx.:> fpscr')
        C.knownRepr
    MP.FP1 name v fpscr -> do
      let sym = s ^. C.stateSymInterface
      v' <- toValBV sym v
      fpscr' <- toValBV sym fpscr
      let args = Ctx.extend (Ctx.extend Ctx.empty v') fpscr'
      fval <- lookupApplySymFun sym sf ("fp_" ++ name) C.knownRepr args C.knownRepr
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.FP2 name v1 v2 fpscr -> do
      let sym = s ^. C.stateSymInterface
      v1' <- toValBV sym v1
      v2' <- toValBV sym v2
      fpscr' <- toValBV sym fpscr
      let args = Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty v1') v2') fpscr'
      fval <- lookupApplySymFun sym sf ("fp_" ++ name) C.knownRepr args C.knownRepr
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.FP3 name v1 v2 v3 fpscr -> do
      let sym = s ^. C.stateSymInterface
      v1' <- toValBV sym v1
      v2' <- toValBV sym v2
      v3' <- toValBV sym v3
      fpscr' <- toValBV sym fpscr
      let args = Ctx.extend (Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty v1') v2') v3') fpscr'
      fval <- lookupApplySymFun sym sf ("fp_" ++ name) C.knownRepr args C.knownRepr
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.Vec1 name v fpscr -> do
      let sym = s ^. C.stateSymInterface
      v' <- toValBV sym v
      fpscr' <- toValBV sym fpscr
      let args = Ctx.extend (Ctx.extend Ctx.empty v') fpscr'
      fval <- lookupApplySymFun sym sf ("vec_" ++ name) C.knownRepr args C.knownRepr
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.Vec2 name v1 v2 fpscr -> do
      let sym = s ^. C.stateSymInterface
      v1' <- toValBV sym v1
      v2' <- toValBV sym v2
      fpscr' <- toValBV sym fpscr
      let args = Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty v1') v2') fpscr'
      fval <- lookupApplySymFun sym sf ("vec_" ++ name) C.knownRepr args C.knownRepr
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.Vec3 name v1 v2 v3 fpscr -> do
      let sym = s ^. C.stateSymInterface
      v1' <- toValBV sym v1
      v2' <- toValBV sym v2
      v3' <- toValBV sym v3
      fpscr' <- toValBV sym fpscr
      let args = Ctx.extend (Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty v1') v2') v3') fpscr'
      fval <- lookupApplySymFun sym sf ("vec_" ++ name) C.knownRepr args C.knownRepr
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)


lookupApplySymFun :: (C.IsSymInterface sym)
                  => sym
                  -> SymFuns sym
                  -> String
                  -> Ctx.Assignment C.BaseTypeRepr ps
                  -> Ctx.Assignment (C.SymExpr sym) ps
                  -> C.BaseTypeRepr r
                  -> IO (C.SymExpr sym r)
lookupApplySymFun sym sf name argReprs args retRepr = do
  r <- IO.readIORef (symFuns sf)
  case M.lookup name r of
    Just (SomeSymFun argReprs' retRepr' fn)
      | Just Refl <- testEquality argReprs' argReprs
      , Just Refl <- testEquality retRepr' retRepr -> C.applySymFn sym fn args
      | otherwise -> error (printf "Invalid type for symbolic function '%s' expected %s but got %s " name (show (argReprs, retRepr)) (show (argReprs', retRepr')))
    Nothing -> do
      case C.userSymbol name of
        Left _ -> X.throwIO (NonUserSymbol name)
        Right nameSymbol -> do
          fn <- C.freshTotalUninterpFn sym nameSymbol argReprs retRepr
          IO.modifyIORef (symFuns sf) (M.insert name (SomeSymFun argReprs retRepr fn))
          C.applySymFn sym fn args

toValBV :: (C.IsSymInterface sym)
        => sym
        -> A.AtomWrapper (C.RegEntry sym) (MT.BVType w)
        -> IO (C.RegValue sym (C.BVType w))
toValBV sym (A.AtomWrapper x) = LL.projectLLVM_bv sym (C.regValue x)

toValFloat
  :: (C.IsSymInterface sym)
  => sym
  -> A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)
  -> C.RegValue sym (MS.ToCrucibleType (MT.FloatType fi))
toValFloat _ (A.AtomWrapper x) = C.regValue x

withSym
  :: (C.IsSymInterface sym)
  => S p v sym rtp bs r ctx
  -> (sym -> IO a)
  -> IO (a, S p v sym rtp bs r ctx)
withSym s action = do
  let sym = s ^. C.stateSymInterface
  val <- action sym
  return (val, s)

withSymBVUnOp
  :: (C.IsSymInterface sym)
  => S p v sym rtp bs r ctx
  -> A.AtomWrapper (C.RegEntry sym) (MT.BVType w)
  -> (sym -> C.RegValue sym (C.BVType w) -> IO a)
  -> IO (a, S p v sym rtp bs r ctx)
withSymBVUnOp s x action = withSym s $ \sym -> action sym =<< toValBV sym x

withSymFPUnOp
  :: (C.IsSymInterface sym)
  => S p v sym rtp bs r ctx
  -> A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)
  -> (  sym
     -> C.RegValue sym (MS.ToCrucibleType (MT.FloatType fi))
     -> IO a
     )
  -> IO (a, S p v sym rtp bs r ctx)
withSymFPUnOp s x action = withSym s $ \sym -> action sym $ toValFloat sym x

withSymFPBinOp
  :: (C.IsSymInterface sym)
  => S p v sym rtp bs r ctx
  -> A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)
  -> A.AtomWrapper (C.RegEntry sym) (MT.FloatType fi)
  -> (  sym
     -> C.RegValue sym (MS.ToCrucibleType (MT.FloatType fi))
     -> C.RegValue sym (MS.ToCrucibleType (MT.FloatType fi))
     -> IO a
     )
  -> IO (a, S p v sym rtp bs r ctx)
withSymFPBinOp s x y action = withSym s $ \sym -> do
  let x' = toValFloat sym x
  let y' = toValFloat sym y
  action sym x' y'

withRounding
  :: C.IsSymInterface sym
  => sym
  -> A.AtomWrapper (C.RegEntry sym) (MT.BVType 2)
  -> (C.RoundingMode -> IO (C.SymExpr sym tp))
  -> IO (C.SymExpr sym tp)
withRounding sym r action = do
  r' <- toValBV sym r
  U.withRounding sym r' action

type S p v sym rtp bs r ctx = C.CrucibleState p sym (MS.MacawExt (SP.AnyPPC v)) rtp bs r ctx
