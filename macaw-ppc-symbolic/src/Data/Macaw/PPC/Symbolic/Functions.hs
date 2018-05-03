{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.PPC.Symbolic.Functions (
  SymFuns,
  newSymFuns,
  semantics
  ) where

import           GHC.TypeLits

import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Solver.Symbol as C
import qualified Lang.Crucible.Solver.Interface as C
import qualified Lang.Crucible.Types as C

import qualified Lang.Crucible.LLVM.MemModel.Pointer as LL

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.PersistentState as MS
import qualified Data.Macaw.PPC as MP

import qualified Data.Macaw.PPC.Symbolic.AtomWrapper as A

data SymFuns ppc sym =
  SymFuns -- { fnFPIsQNan :: C.SymFn sym (Ctx.EmptyCtx Ctx.::>

newSymFuns :: (C.IsSymInterface sym) => sym -> IO (SymFuns ppc sym)
newSymFuns _ = return SymFuns

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

toValBV :: (C.IsSymInterface sym)
        => sym
        -> A.AtomWrapper (C.RegEntry sym) (MT.BVType w)
        -> IO (C.RegValue sym (C.BVType w))
toValBV sym (A.AtomWrapper x) = LL.projectLLVM_bv sym (C.regValue x)

type S ppc sym rtp bs r ctx = C.CrucibleState MS.MacawSimulatorState sym (MS.MacawExt ppc) rtp bs r ctx

