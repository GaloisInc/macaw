{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Macaw.X86.Symbolic
  ( x86_64MacawSymbolicFns
  , x86_64MacawEvalFn
  , SymFuns, newSymFuns
  ) where

import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC
import           GHC.TypeLits
import           Data.Functor.Identity(Identity(..))

import qualified Data.Macaw.CFG as M
import           Data.Macaw.Symbolic
import           Data.Macaw.Symbolic.PersistentState(typeToCrucible)
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.X86 as M
import qualified Data.Macaw.X86.X86Reg as M
import           Data.Macaw.X86.Crucible
import qualified Flexdis86.Register as F

import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.Solver.Symbol as C
import qualified Lang.Crucible.Solver.Interface as C




------------------------------------------------------------------------
-- Utilities for generating a type-level context with repeated elements.

type family CtxRepeat (n :: Nat) (c :: k) :: Ctx k where
  CtxRepeat  0 c = EmptyCtx
  CtxRepeat  n c = CtxRepeat  (n-1) c ::> c

class RepeatAssign (tp :: k) (ctx :: Ctx k) where
  repeatAssign :: (Int -> f tp) -> Assignment f ctx

instance RepeatAssign tp EmptyCtx where
  repeatAssign _ = Empty

instance RepeatAssign tp ctx => RepeatAssign tp (ctx ::> tp) where
  repeatAssign f =
    let r = repeatAssign f
     in r :> f (sizeInt (Ctx.size r))

------------------------------------------------------------------------
-- X86 Registers

type instance ArchRegContext M.X86_64
   =   (EmptyCtx ::> M.BVType 64)
   <+> CtxRepeat 16 (M.BVType 64)
   <+> CtxRepeat 9  M.BoolType
   <+> CtxRepeat 16  M.BoolType
   <+> (EmptyCtx ::> M.BVType 3)
   <+> CtxRepeat 8 (M.BVType 2)
   <+> CtxRepeat 8 (M.BVType 80)
   <+> CtxRepeat 16 (M.BVType 256)

x86RegName :: M.X86Reg tp -> C.SolverSymbol
x86RegName M.X86_IP     = C.systemSymbol "!ip"
x86RegName (M.X86_GP r) = C.systemSymbol $ "!" ++ show r
x86RegName (M.X86_FlagReg r) = C.systemSymbol $ "!" ++ show r
x86RegName (M.X87_StatusReg r) = C.systemSymbol $ "!x87Status" ++ show r
x86RegName M.X87_TopReg = C.systemSymbol $ "!x87Top"
x86RegName (M.X87_TagReg r) = C.systemSymbol $ "!x87Tag" ++ show r
x86RegName (M.X87_FPUReg r) = C.systemSymbol $ "!" ++ show r
x86RegName (M.X86_YMMReg r) = C.systemSymbol $ "!" ++ show r

gpReg :: Int -> M.X86Reg (M.BVType 64)
gpReg = M.X86_GP . F.Reg64 . fromIntegral

-- | The x86 flag registers that are directly supported by Macw.
flagRegs :: Assignment M.X86Reg (CtxRepeat 9 M.BoolType)
flagRegs =
  Empty :> M.CF :> M.PF :> M.AF :> M.ZF :> M.SF :> M.TF :> M.IF :> M.DF :> M.OF

-- | This contains an assignment that stores the register associated with each index in the
-- X86 register structure.
x86RegAssignment :: Assignment M.X86Reg (ArchRegContext M.X86_64)
x86RegAssignment =
  Empty :> M.X86_IP
  <++> (repeatAssign gpReg :: Assignment M.X86Reg (CtxRepeat 16 (M.BVType 64)))
  <++> flagRegs
  <++> (repeatAssign (M.X87_StatusReg . fromIntegral) :: Assignment M.X86Reg (CtxRepeat 16 M.BoolType))
  <++> (Empty :> M.X87_TopReg)
  <++> (repeatAssign (M.X87_TagReg . fromIntegral)    :: Assignment M.X86Reg (CtxRepeat  8 (M.BVType 2)))
  <++> (repeatAssign (M.X87_FPUReg . F.mmxReg . fromIntegral) :: Assignment M.X86Reg (CtxRepeat  8 (M.BVType 80)))
  <++> (repeatAssign (M.X86_YMMReg . F.ymmReg . fromIntegral) :: Assignment M.X86Reg (CtxRepeat 16 (M.BVType 256)))

------------------------------------------------------------------------
-- Other X86 specific


-- | We currently make a type like this, we could instead a generic
-- X86PrimFn function
data X86StmtExtension (f :: C.CrucibleType -> *) (ctp :: C.CrucibleType) where
  -- | To reduce clutter, but potentially increase clutter, we just make every
  -- Macaw X86PrimFn a Macaw-Crucible statement extension.
  X86PrimFn :: !(M.X86PrimFn (AtomWrapper f) t) ->
                                        X86StmtExtension f (ToCrucibleType t)



instance C.PrettyApp X86StmtExtension where
  ppApp ppSub (X86PrimFn x) = d
    where Identity d = M.ppArchFn (Identity . liftAtomIn ppSub) x

instance C.TypeApp X86StmtExtension where
  appType (X86PrimFn x) = typeToCrucible (M.typeRepr x)

instance FunctorFC X86StmtExtension where
  fmapFC f (X86PrimFn x) = X86PrimFn (fmapFC (liftAtomMap f) x)

instance FoldableFC X86StmtExtension where
  foldMapFC f (X86PrimFn x) = foldMapFC (liftAtomIn f) x

instance TraversableFC X86StmtExtension where
  traverseFC f (X86PrimFn x) = X86PrimFn <$> traverseFC (liftAtomTrav f) x

type instance MacawArchStmtExtension M.X86_64 = X86StmtExtension


crucGenX86Fn :: forall ids s tp. M.X86PrimFn (M.Value M.X86_64 ids) tp
             -> CrucGen M.X86_64 ids s (C.Atom s (ToCrucibleType tp))
crucGenX86Fn fn = do
  let f ::  M.Value arch ids a -> CrucGen arch ids s (AtomWrapper (C.Atom s) a)
      f x = AtomWrapper <$> valueToCrucible x
  r <- traverseFC f fn
  evalArchStmt (X86PrimFn r)


crucGenX86Stmt :: M.X86Stmt (M.Value M.X86_64 ids)
                 -> CrucGen M.X86_64 ids s ()
crucGenX86Stmt stmt =
  case stmt of
    _ -> error $ "crucGenX86Stmt does not yet support " ++ show (M.ppArchStmt (M.ppValue 0) stmt)

crucGenX86TermStmt :: M.X86TermStmt ids
                   -> M.RegState M.X86Reg (M.Value M.X86_64 ids)
                   -> CrucGen M.X86_64 ids s ()
crucGenX86TermStmt tstmt regs =
  case tstmt of
    _ -> undefined regs

-- | X86_64 specific functions for translation Macaw into Crucible.
x86_64MacawSymbolicFns :: MacawSymbolicArchFunctions M.X86_64
x86_64MacawSymbolicFns =
  MacawSymbolicArchFunctions
  { crucGenArchConstraints = \x -> x
  , crucGenRegAssignment = x86RegAssignment
  , crucGenArchRegName  = x86RegName
  , crucGenArchFn = crucGenX86Fn
  , crucGenArchStmt = crucGenX86Stmt
  , crucGenArchTermStmt = crucGenX86TermStmt
  }


-- | X86_64 specific function for evaluating a Macaw X86_64 program in Crucible.
x86_64MacawEvalFn ::
  C.IsSymInterface sym => SymFuns sym -> MacawArchEvalFn sym M.X86_64
x86_64MacawEvalFn fs (X86PrimFn x) s = semantics fs x s

