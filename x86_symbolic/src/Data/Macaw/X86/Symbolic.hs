{-# LANGUAGE TypeFamilies #-}
module Data.Macaw.X86.Symbolic
  ( x86TranslateFunctions
  ) where

import qualified Data.Macaw.CFG as M
import           Data.Macaw.Symbolic
import qualified Data.Macaw.X86 as M
import           Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.Solver.Symbol as C

type instance ArchRegContext M.X86_64
   = EmptyCtx -- TODO: Fix this

x86RegName :: M.X86Reg tp -> C.SolverSymbol
x86RegName = undefined

x86RegAssignment :: Assignment M.X86Reg (ArchRegContext M.X86_64)
x86RegAssignment = undefined


crucGenX86Fn :: M.X86PrimFn (M.Value M.X86_64 ids) tp
             -> CrucGen M.X86_64 ids s (C.Atom s (ToCrucibleType tp))
crucGenX86Fn = undefined

crucGenX86Stmt :: M.X86Stmt (M.Value M.X86_64 ids)
                 -> CrucGen M.X86_64 ids s ()
crucGenX86Stmt = undefined

crucGenX86TermStmt :: M.X86TermStmt ids
                   -> M.RegState M.X86Reg (M.Value M.X86_64 ids)
                   -> CrucGen M.X86_64 ids s ()
crucGenX86TermStmt = undefined

-- | The symbolic tra
x86TranslateFunctions :: CrucGenArchFunctions M.X86_64
x86TranslateFunctions =
  CrucGenArchFunctions
  { crucGenArchConstraints = \x -> x
  , crucGenRegAssignment = x86RegAssignment
  , crucGenArchRegName  = x86RegName
  , crucGenArchFn = crucGenX86Fn
  , crucGenArchStmt = crucGenX86Stmt
  , crucGenArchTermStmt = crucGenX86TermStmt
  }
