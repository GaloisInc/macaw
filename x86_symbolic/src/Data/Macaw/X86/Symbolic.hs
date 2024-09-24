{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.X86.Symbolic
  ( x86_64MacawSymbolicFns
  , x86_64MacawEvalFn
  , SymFuns(..), newSymFuns
  , X86StmtExtension(..)

  , x86RegAssignment
  , lookupX86Reg
  , updateX86Reg
  , freshX86Reg

  , RegAssign
  , getReg
  , IP, GP, Flag, X87Status, X87Top, X87Tag, FPReg, YMM
  , Rip, Rax, Rcx, Rdx, Rbx, Rsp, Rbp, Rsi, Rdi
  , R8, R9, R10, R11, R12, R13, R14, R15
  , CF, PF, AF, ZF, SF, TF, IF, DF, OF
  , IE, DE, ZE, OE, UE, PE, EF, ES, C0, C1, C2, C3
  , rip, rax, rbx, rcx, rdx, rsp, rbp, rsi, rdi
  , r8, r9, r10, r11, r12, r13, r14, r15
  , cf, pf, af, zf, sf, tf, if_, df, of_
  , ie, de, ze, oe, ue, pe, ef, es, c0, c1, c2, c3
  ) where

import           Control.Monad ( void )
import           Control.Monad.IO.Class ( liftIO )
import           Data.Functor.Identity (Identity(..))
import           Data.Kind
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC

import qualified Data.Macaw.CFG as M
import           Data.Macaw.Symbolic
import           Data.Macaw.Symbolic.Backend
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.X86 as M
import           Data.Macaw.X86.Crucible
import qualified Data.Macaw.X86.Symbolic.Panic as P

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.CFG.Expr as CE
import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.LLVM.MemModel as MM

import           Data.Macaw.X86.Symbolic.Regs

------------------------------------------------------------------------
-- Other X86 specific


-- | We currently make a type like this, we could instead a generic
-- X86PrimFn function
data X86StmtExtension (f :: C.CrucibleType -> Type) (ctp :: C.CrucibleType) where
  -- | To reduce clutter, but potentially increase clutter, we just make every
  -- Macaw X86PrimFn a Macaw-Crucible statement extension.
  X86PrimFn :: !(M.X86PrimFn (AtomWrapper f) t) ->
                                        X86StmtExtension f (ToCrucibleType t)
  X86PrimStmt :: !(M.X86Stmt (AtomWrapper f))
              -> X86StmtExtension f C.UnitType
  X86PrimTerm :: !(M.X86TermStmt (AtomWrapper f)) -> X86StmtExtension f C.UnitType

instance C.PrettyApp X86StmtExtension where
  ppApp ppSub (X86PrimFn x) = d
    where Identity d = M.ppArchFn (Identity . liftAtomIn ppSub) x
  ppApp ppSub (X86PrimStmt stmt) = M.ppArchStmt (liftAtomIn ppSub) stmt
  ppApp ppSub (X86PrimTerm term) = M.ppArchTermStmt (liftAtomIn ppSub) term

instance C.TypeApp X86StmtExtension where
  appType (X86PrimFn x) = typeToCrucible (M.typeRepr x)
  appType (X86PrimStmt _) = C.UnitRepr
  appType (X86PrimTerm _) = C.UnitRepr

instance FunctorFC X86StmtExtension where
  fmapFC f (X86PrimFn x) = X86PrimFn (fmapFC (liftAtomMap f) x)
  fmapFC f (X86PrimStmt stmt) = X86PrimStmt (fmapF (liftAtomMap f) stmt)
  fmapFC f (X86PrimTerm term) = X86PrimTerm (fmapF (liftAtomMap f) term)

instance FoldableFC X86StmtExtension where
  foldMapFC f (X86PrimFn x) = foldMapFC (liftAtomIn f) x
  foldMapFC f (X86PrimStmt stmt) = foldMapF (liftAtomIn f) stmt
  -- There are no contents in terminator statements for now
  foldMapFC _f (X86PrimTerm _term) = mempty

instance TraversableFC X86StmtExtension where
  traverseFC f (X86PrimFn x) = X86PrimFn <$> traverseFC (liftAtomTrav f) x
  traverseFC f (X86PrimStmt stmt) = X86PrimStmt <$> traverseF (liftAtomTrav f) stmt
  traverseFC f (X86PrimTerm term) = X86PrimTerm <$> traverseF (liftAtomTrav f) term

type instance MacawArchStmtExtension M.X86_64 = X86StmtExtension


crucGenX86Fn :: forall ids s tp. M.X86PrimFn (M.Value M.X86_64 ids) tp
             -> CrucGen M.X86_64 ids s (C.Atom s (ToCrucibleType tp))
crucGenX86Fn fn =
  case fn of
    M.X86Syscall w v1 v2 v3 v4 v5 v6 v7 -> do
      -- This is the key mechanism for our system call handling. See Note
      -- [Syscalls] for details
      a1 <- valueToCrucible v1
      a2 <- valueToCrucible v2
      a3 <- valueToCrucible v3
      a4 <- valueToCrucible v4
      a5 <- valueToCrucible v5
      a6 <- valueToCrucible v6
      a7 <- valueToCrucible v7

      let syscallArgs = Ctx.Empty Ctx.:> a1 Ctx.:> a2 Ctx.:> a3 Ctx.:> a4 Ctx.:> a5 Ctx.:> a6 Ctx.:> a7
      let argTypes = Ctx.Empty Ctx.:> MM.LLVMPointerRepr w Ctx.:> MM.LLVMPointerRepr w Ctx.:> MM.LLVMPointerRepr w Ctx.:> MM.LLVMPointerRepr w Ctx.:> MM.LLVMPointerRepr w Ctx.:> MM.LLVMPointerRepr w Ctx.:> MM.LLVMPointerRepr w
      let retTypes = Ctx.Empty Ctx.:> MM.LLVMPointerRepr w Ctx.:> MM.LLVMPointerRepr w
      let retRepr = C.StructRepr retTypes
      syscallArgStructAtom <- evalAtom (C.EvalApp (CE.MkStruct argTypes syscallArgs))
      let lookupHdlStmt = MacawLookupSyscallHandle argTypes retTypes syscallArgStructAtom
      hdlAtom <- evalMacawStmt lookupHdlStmt
      evalAtom $ C.Call hdlAtom syscallArgs retRepr
    _ -> do
      let f :: forall arch a . M.Value arch ids a -> CrucGen arch ids s (AtomWrapper (C.Atom s) a)
          f x = AtomWrapper <$> valueToCrucible x
      r <- traverseFC f fn
      evalArchStmt (X86PrimFn r)


crucGenX86Stmt :: forall ids s
                . M.X86Stmt (M.Value M.X86_64 ids)
               -> CrucGen M.X86_64 ids s ()
crucGenX86Stmt stmt = do
  let f :: M.Value M.X86_64 ids a -> CrucGen M.X86_64 ids s (AtomWrapper (C.Atom s) a)
      f x = AtomWrapper <$> valueToCrucible x
  stmt' <- traverseF f stmt
  void (evalArchStmt (X86PrimStmt stmt'))

crucGenX86TermStmt :: forall ids s
                    . M.X86TermStmt (M.Value M.X86_64 ids)
                   -> M.RegState M.X86Reg (M.Value M.X86_64 ids)
                   -> Maybe (C.Label s)
                   -> CrucGen M.X86_64 ids s ()
crucGenX86TermStmt tstmt _regs _fallthrough = do
  tstmt' <- traverseF f tstmt
  void (evalArchStmt (X86PrimTerm tstmt'))
  where
    f :: M.Value M.X86_64 ids a -> CrucGen M.X86_64 ids s (AtomWrapper (C.Atom s) a)
    f x = AtomWrapper <$> valueToCrucible x

-- | X86_64 specific functions for translation Macaw into Crucible.
x86_64MacawSymbolicFns :: MacawSymbolicArchFunctions M.X86_64
x86_64MacawSymbolicFns =
  MacawSymbolicArchFunctions
  { crucGenArchConstraints = \x -> x
  , crucGenRegAssignment = x86RegAssignment
  , crucGenRegStructType = x86RegStructType
  , crucGenArchRegName  = x86RegName
  , crucGenArchFn = crucGenX86Fn
  , crucGenArchStmt = crucGenX86Stmt
  , crucGenArchTermStmt = crucGenX86TermStmt
  }


-- | X86_64 specific function for evaluating a Macaw X86_64 program in Crucible.
x86_64MacawEvalFn
  :: (C.IsSymInterface sym, MM.HasLLVMAnn sym, ?memOpts :: MM.MemOptions)
  => SymFuns sym
  -> MacawArchStmtExtensionOverride M.X86_64
  -> MacawArchEvalFn p sym MM.Mem M.X86_64
x86_64MacawEvalFn fs (MacawArchStmtExtensionOverride override) =
  MacawArchEvalFn $ \global_var_mem globals ext_stmt crux_state -> do
    mRes <- override ext_stmt crux_state
    case mRes of
      Nothing ->
        case ext_stmt of
          X86PrimFn x -> funcSemantics fs x crux_state
          X86PrimStmt stmt -> stmtSemantics fs global_var_mem globals stmt crux_state
          X86PrimTerm term -> termSemantics fs term crux_state
      Just res -> return res

x86LookupReg
  :: C.RegEntry sym (ArchRegStruct M.X86_64)
  -> M.X86Reg tp
  -> C.RegEntry sym (ToCrucibleType tp)
x86LookupReg reg_struct_entry macaw_reg =
  case lookupX86Reg macaw_reg (C.regValue reg_struct_entry) of
    Just (C.RV val) -> C.RegEntry (typeToCrucible $ M.typeRepr macaw_reg) val
    Nothing -> P.panic
                 P.X86_64
                 "x86LookupReg"
                 ["unexpected register: " ++ showF macaw_reg]

x86UpdateReg
  :: C.RegEntry sym (ArchRegStruct M.X86_64)
  -> M.X86Reg tp
  -> C.RegValue sym (ToCrucibleType tp)
  -> C.RegEntry sym (ArchRegStruct M.X86_64)
x86UpdateReg reg_struct_entry macaw_reg val =
  case updateX86Reg macaw_reg (\_ -> C.RV val) (C.regValue reg_struct_entry) of
    Just res_reg_struct -> reg_struct_entry { C.regValue = res_reg_struct }
    Nothing -> P.panic
                 P.X86_64
                 "x86UpdateReg"
                 ["unexpected register: " ++ showF macaw_reg]

instance GenArchInfo LLVMMemory M.X86_64 where
  genArchVals _ _ mOverride = Just $ GenArchVals
    { archFunctions = x86_64MacawSymbolicFns
    , withArchEval = \sym k -> do
        sfns <- liftIO $ newSymFuns sym
        let override = case mOverride of
                         Nothing -> defaultMacawArchStmtExtensionOverride
                         Just ov -> ov
        k $ x86_64MacawEvalFn sfns override
    , withArchConstraints = \x -> x
    , lookupReg = x86LookupReg
    , updateReg = x86UpdateReg
    }

{- Note [Syscalls]

While most of the extension functions can be translated directly by embedding them in
macaw symbolic wrappers (e.g., X86PrimFn), system calls are different. We cannot
symbolically branch (and thus cannot invoke overrides) from extension
statement/expression handlers, which is significantly limiting when modeling
operating system behavior.

To work around this, we translate the literal system call extension function
into a sequence that gives us more flexibility:

1. Inspect the machine state and return the function handle that corresponds to
   the requested syscall
2. Invoke the syscall

Note that the ability of system calls to modify the register state (i.e., return
values), the translation of the machine instruction must arrange for the
returned values to flow back into the required registers. For example, it means
that the two return registers (rax and rdi) have to be updated with the new
values returned by the overrides on Linux/x86_64. macaw-x86 arranges for that to
happen when it generates an 'X86Syscall' instruction.

This subtle coupling is required because register identities are lost at this
stage in the translation, and this code cannot force an update on a machine
register.

Note that after this stage, there are no more 'X86Syscall' expressions.

-}
