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
  semantics,
  -- * Exceptions
  SemanticsError(..)
  ) where

import           GHC.TypeLits

import qualified Control.Exception as X
import qualified Data.IORef as IO
import qualified Data.Map.Strict as M
import           Data.Parameterized.Classes ( (:~:)( Refl ), testEquality )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import           Text.Printf ( printf )

import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Solver.Symbol as C
import qualified Lang.Crucible.Solver.Interface as C
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LL

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.PPC as MP

import qualified Data.Macaw.PPC.Symbolic.AtomWrapper as A

data SomeSymFun sym where
  SomeSymFun :: Ctx.Assignment C.BaseTypeRepr ps -> C.BaseTypeRepr r -> C.SymFn sym ps r -> SomeSymFun sym

data SymFuns ppc sym =
  SymFuns { symFuns :: IO.IORef (M.Map String (SomeSymFun sym))
          }

newSymFuns :: forall sym ppc . (C.IsSymInterface sym) => sym -> IO (SymFuns ppc sym)
newSymFuns _sym = do
  r <- IO.newIORef M.empty
  return SymFuns { symFuns = r
                 }

data SemanticsError = NonUserSymbol String
  deriving (Show)

instance X.Exception SemanticsError

semantics :: (C.IsSymInterface sym, MS.ToCrucibleType mt ~ t, 1 <= MC.ArchAddrWidth ppc)
          => SymFuns ppc sym
          -> MP.PPCPrimFn ppc (A.AtomWrapper (C.RegEntry sym)) mt
          -> S ppc sym rtp bs r ctx
          -> IO (C.RegValue sym t, S ppc sym rtp bs r ctx)
semantics sf pf s =
  case pf of
    MP.UDiv _rep lhs rhs -> do
      let sym = C.stateSymInterface s
      lhs' <- toValBV sym lhs
      rhs' <- toValBV sym rhs
      v <- LL.llvmPointer_bv sym =<< C.bvUdiv sym lhs' rhs'
      return (v, s)
    MP.SDiv _rep lhs rhs -> do
      let sym = C.stateSymInterface s
      lhs' <- toValBV sym lhs
      rhs' <- toValBV sym rhs
      v <- LL.llvmPointer_bv sym =<< C.bvSdiv sym lhs' rhs'
      return (v, s)
    MP.FP1 name v fpscr -> do
      let sym = C.stateSymInterface s
      v' <- toValBV sym v
      fpscr' <- toValBV sym fpscr
      let argTypes = Ctx.extend (Ctx.extend Ctx.empty (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @32))
      let args = Ctx.extend (Ctx.extend Ctx.empty v') fpscr'
      let rType = C.BaseBVRepr (NR.knownNat @160)
      fval <- lookupApplySymFun sym sf name argTypes args rType
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.FP2 name v1 v2 fpscr -> do
      let sym = C.stateSymInterface s
      v1' <- toValBV sym v1
      v2' <- toValBV sym v2
      fpscr' <- toValBV sym fpscr
      let argTypes = Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @32))
      let args = Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty v1') v2') fpscr'
      let rType = C.BaseBVRepr (NR.knownNat @160)
      fval <- lookupApplySymFun sym sf name argTypes args rType
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.FP3 name v1 v2 v3 fpscr -> do
      let sym = C.stateSymInterface s
      v1' <- toValBV sym v1
      v2' <- toValBV sym v2
      v3' <- toValBV sym v3
      fpscr' <- toValBV sym fpscr
      let argTypes = Ctx.extend (Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @32))
      let args = Ctx.extend (Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty v1') v2') v3') fpscr'
      let rType = C.BaseBVRepr (NR.knownNat @160)
      fval <- lookupApplySymFun sym sf name argTypes args rType
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.Vec1 name v fpscr -> do
      let sym = C.stateSymInterface s
      v' <- toValBV sym v
      fpscr' <- toValBV sym fpscr
      let argTypes = Ctx.extend (Ctx.extend Ctx.empty (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @32))
      let args = Ctx.extend (Ctx.extend Ctx.empty v') fpscr'
      let rType = C.BaseBVRepr (NR.knownNat @160)
      fval <- lookupApplySymFun sym sf name argTypes args rType
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.Vec2 name v1 v2 fpscr -> do
      let sym = C.stateSymInterface s
      v1' <- toValBV sym v1
      v2' <- toValBV sym v2
      fpscr' <- toValBV sym fpscr
      let argTypes = Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @32))
      let args = Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty v1') v2') fpscr'
      let rType = C.BaseBVRepr (NR.knownNat @160)
      fval <- lookupApplySymFun sym sf name argTypes args rType
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.Vec3 name v1 v2 v3 fpscr -> do
      let sym = C.stateSymInterface s
      v1' <- toValBV sym v1
      v2' <- toValBV sym v2
      v3' <- toValBV sym v3
      fpscr' <- toValBV sym fpscr
      let argTypes = Ctx.extend (Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @32))
      let args = Ctx.extend (Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty v1') v2') v3') fpscr'
      let rType = C.BaseBVRepr (NR.knownNat @160)
      fval <- lookupApplySymFun sym sf name argTypes args rType
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.FPIsQNaN {} -> error "FPIsQNaN is not supported yet (unused?)"
    MP.FPIsSNaN {} -> error "FPIsSNaN is not supported yet (unused?)"
    MP.FPCvt {} -> error "FPCvt is not supported yet (unused?)"


lookupApplySymFun :: (C.IsSymInterface sym)
                  => sym
                  -> SymFuns ppc sym
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

type S ppc sym rtp bs r ctx = C.CrucibleState MS.MacawSimulatorState sym (MS.MacawExt ppc) rtp bs r ctx

