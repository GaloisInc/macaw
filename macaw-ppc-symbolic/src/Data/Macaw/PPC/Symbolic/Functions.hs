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
import qualified Data.Parameterized.NatRepr as NR
import           Text.Printf ( printf )

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.LLVM.MemModel as LL
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C
import qualified Lang.Crucible.Types as C
import qualified What4.Interface as C
import qualified What4.Symbol as C

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

termSemantics :: (C.IsSymInterface sym, 1 <= MC.ArchAddrWidth ppc)
              => SymFuns ppc sym
              -> MP.PPCTermStmt ids
              -> S ppc sym rtp bs r ctx
              -> IO (C.RegValue sym C.UnitType, S ppc sym rtp bs r ctx)
termSemantics = error "PowerPC-specific terminator statement semantics not yet implemented"

stmtSemantics :: (C.IsSymInterface sym, 1 <= MC.ArchAddrWidth ppc)
              => SymFuns ppc sym
              -> MP.PPCStmt ppc (A.AtomWrapper (C.RegEntry sym))
              -> S ppc sym rtp bs r ctx
              -> IO (C.RegValue sym C.UnitType, S ppc sym rtp bs r ctx)
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

funcSemantics :: (C.IsSymInterface sym, MS.ToCrucibleType mt ~ t, 1 <= MC.ArchAddrWidth ppc)
              => SymFuns ppc sym
              -> MP.PPCPrimFn ppc (A.AtomWrapper (C.RegEntry sym)) mt
              -> S ppc sym rtp bs r ctx
              -> IO (C.RegValue sym t, S ppc sym rtp bs r ctx)
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
    MP.FP1 name v fpscr -> do
      let sym = s ^. C.stateSymInterface
      v' <- toValBV sym v
      fpscr' <- toValBV sym fpscr
      let argTypes = Ctx.extend (Ctx.extend Ctx.empty (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @32))
      let args = Ctx.extend (Ctx.extend Ctx.empty v') fpscr'
      let rType = C.BaseBVRepr (NR.knownNat @160)
      fval <- lookupApplySymFun sym sf name argTypes args rType
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.FP2 name v1 v2 fpscr -> do
      let sym = s ^. C.stateSymInterface
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
      let sym = s ^. C.stateSymInterface
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
      let sym = s ^. C.stateSymInterface
      v' <- toValBV sym v
      fpscr' <- toValBV sym fpscr
      let argTypes = Ctx.extend (Ctx.extend Ctx.empty (C.BaseBVRepr (NR.knownNat @128))) (C.BaseBVRepr (NR.knownNat @32))
      let args = Ctx.extend (Ctx.extend Ctx.empty v') fpscr'
      let rType = C.BaseBVRepr (NR.knownNat @160)
      fval <- lookupApplySymFun sym sf name argTypes args rType
      ptrVal <- LL.llvmPointer_bv sym fval
      return (ptrVal, s)
    MP.Vec2 name v1 v2 fpscr -> do
      let sym = s ^. C.stateSymInterface
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
      let sym = s ^. C.stateSymInterface
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

type S ppc sym rtp bs r ctx = C.CrucibleState (MS.MacawSimulatorState sym) sym (MS.MacawExt ppc) rtp bs r ctx
