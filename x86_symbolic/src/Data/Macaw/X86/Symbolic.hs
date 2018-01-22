{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.X86.Symbolic
  ( x86_64MacawSymbolicFns
  ) where

import           Control.Monad.Identity
import           Data.Parameterized.Context as Ctx
import           GHC.TypeLits

import qualified Data.Macaw.CFG as M
import           Data.Macaw.Symbolic
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.X86 as M
import qualified Data.Macaw.X86.X86Reg as M
import qualified Flexdis86.Register as F

import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.Solver.Symbol as C

------------------------------------------------------------------------
-- Utilities for generating a type-level context with repeated elements.

type family CtxRepeat (n :: Nat) (c :: k) :: Ctx k where
  CtxRepeat  0 c = EmptyCtx
  CtxRepeat  1 c = CtxRepeat  0 c ::> c
  CtxRepeat  2 c = CtxRepeat  1 c ::> c
  CtxRepeat  3 c = CtxRepeat  2 c ::> c
  CtxRepeat  4 c = CtxRepeat  3 c ::> c
  CtxRepeat  5 c = CtxRepeat  4 c ::> c
  CtxRepeat  6 c = CtxRepeat  5 c ::> c
  CtxRepeat  7 c = CtxRepeat  6 c ::> c
  CtxRepeat  8 c = CtxRepeat  7 c ::> c
  CtxRepeat  9 c = CtxRepeat  8 c ::> c
  CtxRepeat 10 c = CtxRepeat  9 c ::> c
  CtxRepeat 11 c = CtxRepeat 10 c ::> c
  CtxRepeat 12 c = CtxRepeat 11 c ::> c
  CtxRepeat 13 c = CtxRepeat 12 c ::> c
  CtxRepeat 14 c = CtxRepeat 13 c ::> c
  CtxRepeat 15 c = CtxRepeat 14 c ::> c
  CtxRepeat 16 c = CtxRepeat 15 c ::> c

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

crucGenX86Fn :: M.X86PrimFn (M.Value M.X86_64 ids) tp
             -> CrucGen M.X86_64 ids s (C.Atom s (ToCrucibleType tp))
crucGenX86Fn fn =
  case fn of
    _ -> error $
      "crucGenX86Fn does not yet support: " ++ show (runIdentity (M.ppArchFn (pure . M.ppValue 0)  fn))

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

-- | The symbolic tra
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
