{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.PPC.Symbolic (
  ppcMacawSymbolicFns,
  ppcMacawEvalFn,
  F.SymFuns,
  F.newSymFuns,
  F.SemanticsError(..),
  ) where

import           GHC.TypeLits

import           Control.Monad ( void )
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.Functor.Identity as I
import qualified Data.Kind as DK
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as FC
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.LLVM.MemModel as Mem
import qualified Lang.Crucible.Types as C

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Backend as MSB
import qualified Lang.Crucible.Simulator.RegMap as MCR
import qualified Lang.Crucible.Simulator.RegValue as MCRV
import qualified Data.Macaw.PPC as MP
import qualified SemMC.Architecture.PPC as SP

import qualified Data.Macaw.PPC.Symbolic.AtomWrapper as A
import qualified Data.Macaw.PPC.Symbolic.Functions as F
import qualified Data.Macaw.PPC.Symbolic.Panic as P
import qualified Data.Macaw.PPC.Symbolic.Regs as Regs

ppcMacawSymbolicFns :: ( SP.KnownVariant v
                       , 1 <= SP.AddrWidth v
                       , MC.MemWidth (SP.AddrWidth v)
                       ) => MS.MacawSymbolicArchFunctions (SP.AnyPPC v)
ppcMacawSymbolicFns =
  MSB.MacawSymbolicArchFunctions
  { MSB.crucGenArchConstraints = \x -> x
  , MSB.crucGenArchRegName = Regs.ppcRegName
  , MSB.crucGenRegAssignment = Regs.ppcRegAssignment
  , MSB.crucGenRegStructType = Regs.ppcRegStructType
  , MSB.crucGenArchFn = ppcGenFn
  , MSB.crucGenArchStmt = ppcGenStmt
  , MSB.crucGenArchTermStmt = ppcGenTermStmt
  }

ppcMacawEvalFn :: ( C.IsSymInterface sym
                  , 1 <= SP.AddrWidth v
                  )
               => F.SymFuns sym
               -> MS.MacawArchStmtExtensionOverride (SP.AnyPPC v)
               -> MS.MacawArchEvalFn p sym mem (SP.AnyPPC v)
ppcMacawEvalFn fs (MS.MacawArchStmtExtensionOverride override) =
  MSB.MacawArchEvalFn $ \_ _ xt s -> do
    mRes <- override xt s
    case mRes of
      Nothing ->
        case xt of
          PPCPrimFn fn -> F.funcSemantics fs fn s
          PPCPrimStmt stmt -> F.stmtSemantics fs stmt s
          PPCPrimTerm term -> F.termSemantics fs term s
      Just res -> return res


instance MS.IsMemoryModel mem => MS.GenArchInfo mem (SP.AnyPPC SP.V64) where
  genArchVals _ _ mOverride = Just $ MS.GenArchVals
    { MS.archFunctions = ppcMacawSymbolicFns
    , MS.withArchEval = \sym k -> do
        sfns <- liftIO $ F.newSymFuns sym
        let override = case mOverride of
                         Nothing -> MS.defaultMacawArchStmtExtensionOverride
                         Just ov -> ov
        k (ppcMacawEvalFn sfns override)
    , MS.withArchConstraints = \x -> x
    , MS.lookupReg = archLookupReg
    , MS.updateReg = archUpdateReg
    }

instance MS.IsMemoryModel mem => MS.GenArchInfo mem (SP.AnyPPC SP.V32) where
  genArchVals _ _ mOverride = Just $ MS.GenArchVals
    { MS.archFunctions = ppcMacawSymbolicFns
    , MS.withArchEval = \sym k -> do
        sfns <- liftIO $ F.newSymFuns sym
        let override = case mOverride of
                         Nothing -> MS.defaultMacawArchStmtExtensionOverride
                         Just ov -> ov
        k (ppcMacawEvalFn sfns override)
    , MS.withArchConstraints = \x -> x
    , MS.lookupReg = archLookupReg
    , MS.updateReg = archUpdateReg
    }

archLookupReg :: ( MP.KnownVariant v
                 , ppc ~ MP.AnyPPC v
                 ) =>
                 MCR.RegEntry sym (MS.ArchRegStruct (MP.AnyPPC v))
              -> MP.PPCReg v tp
              -> MCR.RegEntry sym (MS.ToCrucibleType tp)
archLookupReg regEntry reg =
  case Regs.lookupReg reg (MCR.regValue regEntry) of
    Just (MCRV.RV val) -> MCR.RegEntry (MS.typeToCrucible $ MT.typeRepr reg) val
    Nothing -> P.panic
                 P.PPC
                 "archLookupReg"
                 ["unexpected register: " ++ show (MC.prettyF reg)]

archUpdateReg :: ( MP.KnownVariant v
                 , ppc ~ MP.AnyPPC v
                 ) =>
                 MCR.RegEntry sym (MS.ArchRegStruct (MP.AnyPPC v))
              -> MP.PPCReg v tp
              -> MCRV.RegValue sym (MS.ToCrucibleType tp)
              -> MCR.RegEntry sym (MS.ArchRegStruct (MP.AnyPPC v))
archUpdateReg regEntry reg val =
  case Regs.updateReg reg (const $ MCRV.RV val) (MCR.regValue regEntry) of
    Just r -> regEntry { MCR.regValue = r }
    Nothing -> P.panic
                 P.PPC
                 "archUpdateReg"
                 ["unexpected register: " ++ show (MC.prettyF reg)]

ppcGenFn :: forall ids s tp v ppc
          . ( ppc ~ MP.AnyPPC v
            , 1 <= SP.AddrWidth v
            )
         => MP.PPCPrimFn v (MC.Value ppc ids) tp
         -> MSB.CrucGen ppc ids s (C.Atom s (MS.ToCrucibleType tp))
ppcGenFn fn =
  case fn of
    MP.PPCSyscall w v0 v3 v4 v5 v6 v7 v8 v9 -> do
      a0 <- MSB.valueToCrucible v0
      a3 <- MSB.valueToCrucible v3
      a4 <- MSB.valueToCrucible v4
      a5 <- MSB.valueToCrucible v5
      a6 <- MSB.valueToCrucible v6
      a7 <- MSB.valueToCrucible v7
      a8 <- MSB.valueToCrucible v8
      a9 <- MSB.valueToCrucible v9

      let syscallArgs = Ctx.Empty Ctx.:> a0 Ctx.:> a3 Ctx.:> a4 Ctx.:> a5 Ctx.:> a6 Ctx.:> a7 Ctx.:> a8 Ctx.:> a9
      let argTypes = Ctx.Empty Ctx.:> Mem.LLVMPointerRepr w
                               Ctx.:> Mem.LLVMPointerRepr w
                               Ctx.:> Mem.LLVMPointerRepr w
                               Ctx.:> Mem.LLVMPointerRepr w
                               Ctx.:> Mem.LLVMPointerRepr w
                               Ctx.:> Mem.LLVMPointerRepr w
                               Ctx.:> Mem.LLVMPointerRepr w
                               Ctx.:> Mem.LLVMPointerRepr w
      -- `retTypes` is a tuple of form (R0, R3) [on PPC32] or (CR, R3) [on PPC64].
      -- Note that this is reversed from the return type of PPCSyscall, which
      -- uses the opposite order. This is because Macaw tuples have the order
      -- of their fields reversed when converted to a Crucible value (see
      -- 'macawListToCrucible' in "Data.Macaw.Symbolic.PersistentState" in
      -- @macaw-symbolic@), so we also reverse the order here to be consistent
      -- with this convention.
      let retTypes = Ctx.Empty Ctx.:> Mem.LLVMPointerRepr (MT.knownNat @32)
                               Ctx.:> Mem.LLVMPointerRepr w
      let retRepr = C.StructRepr retTypes
      syscallArgStructAtom <- MSB.evalAtom (C.EvalApp (C.MkStruct argTypes syscallArgs))
      let lookupHdlStmt = MS.MacawLookupSyscallHandle argTypes retTypes syscallArgStructAtom
      hdlAtom <- MSB.evalMacawStmt lookupHdlStmt
      MSB.evalAtom $! C.Call hdlAtom syscallArgs retRepr
    _ -> do
      let f :: MC.Value ppc ids a -> MSB.CrucGen ppc ids s (A.AtomWrapper (C.Atom s) a)
          f x = A.AtomWrapper <$> MSB.valueToCrucible x
      r <- FC.traverseFC f fn
      MSB.evalArchStmt (PPCPrimFn r)

ppcGenStmt :: forall v ids s ppc
            . ( ppc ~ MP.AnyPPC v )
           => MP.PPCStmt v (MC.Value ppc ids)
           -> MSB.CrucGen ppc ids s ()
ppcGenStmt s = do
  let f :: MC.Value ppc ids a -> MSB.CrucGen ppc ids s (A.AtomWrapper (C.Atom s) a)
      f x = A.AtomWrapper <$> MSB.valueToCrucible x
  s' <- TF.traverseF f s
  void (MSB.evalArchStmt (PPCPrimStmt s'))

ppcGenTermStmt :: forall v ids s ppc
                . ( ppc ~ MP.AnyPPC v )
               => MP.PPCTermStmt v (MC.Value ppc ids)
               -> MC.RegState (MP.PPCReg v) (MC.Value ppc ids)
               -> Maybe (C.Label s)
               -> MSB.CrucGen ppc ids s ()
ppcGenTermStmt ts _rs _fallthrough = do
  ts' <- TF.traverseF f ts
  void (MSB.evalArchStmt (PPCPrimTerm ts'))
  where
    f :: MC.Value ppc ids a -> MSB.CrucGen ppc ids s (A.AtomWrapper (C.Atom s) a)
    f x = A.AtomWrapper <$> MSB.valueToCrucible x

data PPCStmtExtension ppc (f :: C.CrucibleType -> DK.Type) (ctp :: C.CrucibleType) where
  -- | Wrappers around the arch-specific functions in PowerPC; these are
  -- interpreted in 'funcSemantics'.
  PPCPrimFn :: MP.PPCPrimFn ppc (A.AtomWrapper f) t
            -> PPCStmtExtension ppc f (MS.ToCrucibleType t)
  -- | Wrappers around the arch-specific statements in PowerPC; these are
  -- interpreted in 'stmtSemantics'
  PPCPrimStmt :: MP.PPCStmt ppc (A.AtomWrapper f)
              -> PPCStmtExtension ppc f C.UnitType
  -- | Wrappers around the arch-specific terminators in PowerPC; these are
  -- interpreted in 'termSemantics'
  PPCPrimTerm :: MP.PPCTermStmt ppc (A.AtomWrapper f) -> PPCStmtExtension ppc f C.UnitType

instance FC.FunctorFC (PPCStmtExtension ppc) where
  fmapFC f (PPCPrimFn x) = PPCPrimFn (FC.fmapFC (A.liftAtomMap f) x)
  fmapFC f (PPCPrimStmt s) = PPCPrimStmt (TF.fmapF (A.liftAtomMap f) s)
  fmapFC f (PPCPrimTerm t) = PPCPrimTerm (TF.fmapF (A.liftAtomMap f) t)

instance FC.FoldableFC (PPCStmtExtension ppc) where
  foldMapFC f (PPCPrimFn x) = FC.foldMapFC (A.liftAtomIn f) x
  foldMapFC f (PPCPrimStmt s) = TF.foldMapF (A.liftAtomIn f) s
  foldMapFC f (PPCPrimTerm t) = TF.foldMapF (A.liftAtomIn f) t

instance FC.TraversableFC (PPCStmtExtension ppc) where
  traverseFC f (PPCPrimFn x) = PPCPrimFn <$> FC.traverseFC (A.liftAtomTrav f) x
  traverseFC f (PPCPrimStmt s) = PPCPrimStmt <$> TF.traverseF (A.liftAtomTrav f) s
  traverseFC f (PPCPrimTerm t) = PPCPrimTerm <$> TF.traverseF (A.liftAtomTrav f) t

instance (1 <= SP.AddrWidth v) => C.TypeApp (PPCStmtExtension v) where
  appType (PPCPrimFn x) = MS.typeToCrucible (MT.typeRepr x)
  appType (PPCPrimStmt _s) = C.UnitRepr
  appType (PPCPrimTerm _t) = C.UnitRepr

instance C.PrettyApp (PPCStmtExtension v) where
  ppApp ppSub (PPCPrimFn x) =
    I.runIdentity (MC.ppArchFn (I.Identity . A.liftAtomIn ppSub) x)
  ppApp ppSub (PPCPrimStmt s) =
    MC.ppArchStmt (A.liftAtomIn ppSub) s
  ppApp ppSub (PPCPrimTerm t) = MC.ppArchTermStmt (A.liftAtomIn ppSub) t

type instance MSB.MacawArchStmtExtension (MP.AnyPPC v) =
  PPCStmtExtension v
