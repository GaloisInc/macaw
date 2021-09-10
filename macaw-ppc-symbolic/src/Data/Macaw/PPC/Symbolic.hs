{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.PPC.Symbolic (
  ppcMacawSymbolicFns,
  ppcMacawEvalFn,
  F.SymFuns,
  F.newSymFuns,
  getReg,
  lookupReg,
  updateReg,
  -- * Register names
  IP,
  LNK,
  CTR,
  XER,
  CR,
  FPSCR,
  VSCR,
  GP,
  FR,
  -- * Other types
  RegContext
  ) where

import           GHC.TypeLits

import           Control.Lens ( (^.), (%~), (&) )
import           Control.Monad ( void )
import qualified Control.Monad.Catch as X
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.Functor.Identity as I
import qualified Data.Kind as DK
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Typeable ( Typeable )
import qualified Dismantle.PPC as D
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.Types as C
import qualified What4.Interface as C
import qualified What4.Symbol as C

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
import qualified Data.Macaw.PPC.Symbolic.Repeat as R

ppcMacawSymbolicFns :: ( SP.KnownVariant v
                       , 1 <= SP.AddrWidth v
                       , MC.MemWidth (SP.AddrWidth v)
                       ) => MS.MacawSymbolicArchFunctions (SP.AnyPPC v)
ppcMacawSymbolicFns =
  MSB.MacawSymbolicArchFunctions
  { MSB.crucGenArchConstraints = \x -> x
  , MSB.crucGenArchRegName = ppcRegName
  , MSB.crucGenRegAssignment = ppcRegAssignment
  , MSB.crucGenRegStructType = ppcRegStructType
  , MSB.crucGenArchFn = ppcGenFn
  , MSB.crucGenArchStmt = ppcGenStmt
  , MSB.crucGenArchTermStmt = ppcGenTermStmt
  }

type RegSize v = MC.RegAddrWidth (MP.PPCReg v)
type RegContext v
  =     (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- IP
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- LNK
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- CTR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- XER
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)          -- CR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)          -- FPSCR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)          -- VSCR
  C.<+> R.CtxRepeat 32 (MT.BVType (RegSize v))       -- GPRs
  C.<+> R.CtxRepeat 64 (MT.BVType 128)               -- VSRs

type instance MS.ArchRegContext (MP.AnyPPC v) = RegContext v

type RegAssign ppc f = Ctx.Assignment f (MS.ArchRegContext ppc)

type IP = 0
type LNK = 1
type CTR = 2
type XER = 3
type CR = 4
type FPSCR = 5
type VSCR = 6
type GP n = 7 + n
type FR n = 39 + n

getReg :: forall n t f ppc . (Ctx.Idx n (MS.ArchRegContext ppc) t) => RegAssign ppc f -> f t
getReg = (^. (Ctx.field @n))

ppcMacawEvalFn :: ( C.IsSymInterface sym
                  , 1 <= SP.AddrWidth v
                  )
               => F.SymFuns sym
               -> MS.MacawArchEvalFn sym mem (SP.AnyPPC v)
ppcMacawEvalFn fs = MSB.MacawArchEvalFn $ \_ _ _ xt s -> case xt of
  PPCPrimFn fn -> F.funcSemantics fs fn s
  PPCPrimStmt stmt -> F.stmtSemantics fs stmt s
  PPCPrimTerm term -> F.termSemantics fs term s


instance MS.IsMemoryModel mem => MS.GenArchInfo mem (SP.AnyPPC SP.V64) where
  genArchVals _ _ = Just $ MS.GenArchVals
    { MS.archFunctions = ppcMacawSymbolicFns
    , MS.withArchEval = \sym k -> do
        sfns <- liftIO $ F.newSymFuns sym
        k (ppcMacawEvalFn sfns)
    , MS.withArchConstraints = \x -> x
    , MS.lookupReg = archLookupReg
    , MS.updateReg = archUpdateReg
    }

instance MS.IsMemoryModel mem => MS.GenArchInfo mem (SP.AnyPPC SP.V32) where
  genArchVals _ _ = Just $ MS.GenArchVals
    { MS.archFunctions = ppcMacawSymbolicFns
    , MS.withArchEval = \sym k -> do
        sfns <- liftIO $ F.newSymFuns sym
        k (ppcMacawEvalFn sfns)
    , MS.withArchConstraints = \x -> x
    , MS.lookupReg = archLookupReg
    , MS.updateReg = archUpdateReg
    }

ppcRegName :: MP.PPCReg v tp -> C.SolverSymbol
ppcRegName r = C.systemSymbol ("r!" ++ show (MC.prettyF r))

ppcRegAssignment :: forall v
                  . ( MP.KnownVariant v )
                 => Ctx.Assignment (MP.PPCReg v) (RegContext v)
ppcRegAssignment =
  (Ctx.Empty Ctx.:> MP.PPC_IP
            Ctx.:> MP.PPC_LNK
            Ctx.:> MP.PPC_CTR
            Ctx.:> MP.PPC_XER
            Ctx.:> MP.PPC_CR
            Ctx.:> MP.PPC_FPSCR
            Ctx.:> MP.PPC_VSCR)
  Ctx.<++> (R.repeatAssign (MP.PPC_GP . D.GPR . fromIntegral) :: Ctx.Assignment (MP.PPCReg v) (R.CtxRepeat 32 (MT.BVType (RegSize v))))
  Ctx.<++> (R.repeatAssign (MP.PPC_FR . D.VSReg . fromIntegral) :: Ctx.Assignment (MP.PPCReg v) (R.CtxRepeat 64 (MT.BVType 128)))

ppcRegStructType :: forall v
                  . ( MP.KnownVariant v )
                 => C.TypeRepr (MS.ArchRegStruct (MP.AnyPPC v))
ppcRegStructType =
  C.StructRepr (MS.typeCtxToCrucible $ FC.fmapFC MT.typeRepr ppcRegAssignment)

data PPCSymbolicException v = MissingRegisterInState (Some (MP.PPCReg v))

deriving instance Show (PPCSymbolicException v)

instance Typeable v => X.Exception (PPCSymbolicException v)

regIndexMap :: forall v
             . MP.KnownVariant v
            => MSB.RegIndexMap (MP.AnyPPC v)
regIndexMap = MSB.mkRegIndexMap assgn sz
  where
    assgn = ppcRegAssignment @v
    sz = Ctx.size (MS.typeCtxToCrucible (FC.fmapFC MT.typeRepr assgn))

lookupReg :: forall v ppc m f tp
           . (MP.KnownVariant v,
              ppc ~ MP.AnyPPC v,
              X.MonadThrow m)
          => MP.PPCReg v tp
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes ppc)
          -> m (f (MS.ToCrucibleType tp))
lookupReg r asgn =
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn Ctx.! MSB.crucibleIndex pair)

archLookupReg :: ( MP.KnownVariant v
                 , ppc ~ MP.AnyPPC v
                 ) =>
                 MCR.RegEntry sym (MS.ArchRegStruct (MP.AnyPPC v))
              -> MP.PPCReg v tp
              -> MCR.RegEntry sym (MS.ToCrucibleType tp)
archLookupReg regEntry reg =
  case lookupReg reg (MCR.regValue regEntry) of
    Just (MCRV.RV val) -> MCR.RegEntry (MS.typeToCrucible $ MT.typeRepr reg) val
    Nothing -> error $ "unexpected register: " ++ show (MC.prettyF reg)

updateReg :: forall v ppc m f tp
           . (MP.KnownVariant v,
               ppc ~ MP.AnyPPC v,
               X.MonadThrow m)
          => MP.PPCReg v tp
          -> (f (MS.ToCrucibleType tp) -> f (MS.ToCrucibleType tp))
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes ppc)
          -> m (Ctx.Assignment f (MS.MacawCrucibleRegTypes ppc))
updateReg r upd asgn = do
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn & MapF.ixF (MSB.crucibleIndex pair) %~ upd)

archUpdateReg :: ( MP.KnownVariant v
                 , ppc ~ MP.AnyPPC v
                 ) =>
                 MCR.RegEntry sym (MS.ArchRegStruct (MP.AnyPPC v))
              -> MP.PPCReg v tp
              -> MCRV.RegValue sym (MS.ToCrucibleType tp)
              -> MCR.RegEntry sym (MS.ArchRegStruct (MP.AnyPPC v))
archUpdateReg regEntry reg val =
  case updateReg reg (const $ MCRV.RV val) (MCR.regValue regEntry) of
    Just r -> regEntry { MCR.regValue = r }
    Nothing -> error $ "unexpected register: " ++ show (MC.prettyF reg)


ppcGenFn :: forall ids s tp v ppc
          . ( ppc ~ MP.AnyPPC v )
         => MP.PPCPrimFn v (MC.Value ppc ids) tp
         -> MSB.CrucGen ppc ids s (C.Atom s (MS.ToCrucibleType tp))
ppcGenFn fn = do
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
               => MP.PPCTermStmt v ids
               -> MC.RegState (MP.PPCReg v) (MC.Value ppc ids)
               -> MSB.CrucGen ppc ids s ()
ppcGenTermStmt ts _rs =
  void (MSB.evalArchStmt (PPCPrimTerm ts))

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
  PPCPrimTerm :: MP.PPCTermStmt ppc ids -> PPCStmtExtension ppc f C.UnitType

instance FC.FunctorFC (PPCStmtExtension ppc) where
  fmapFC f (PPCPrimFn x) = PPCPrimFn (FC.fmapFC (A.liftAtomMap f) x)
  fmapFC f (PPCPrimStmt s) = PPCPrimStmt (TF.fmapF (A.liftAtomMap f) s)
  fmapFC _f (PPCPrimTerm t) = PPCPrimTerm t

instance FC.FoldableFC (PPCStmtExtension ppc) where
  foldMapFC f (PPCPrimFn x) = FC.foldMapFC (A.liftAtomIn f) x
  foldMapFC f (PPCPrimStmt s) = TF.foldMapF (A.liftAtomIn f) s
  -- There are no contents in any of the terminator statements for now, so there
  -- is no traversal here
  foldMapFC _f (PPCPrimTerm _t) = mempty

instance FC.TraversableFC (PPCStmtExtension ppc) where
  traverseFC f (PPCPrimFn x) = PPCPrimFn <$> FC.traverseFC (A.liftAtomTrav f) x
  traverseFC f (PPCPrimStmt s) = PPCPrimStmt <$> TF.traverseF (A.liftAtomTrav f) s
  traverseFC _f (PPCPrimTerm t) = pure (PPCPrimTerm t)

instance (1 <= SP.AddrWidth v) => C.TypeApp (PPCStmtExtension v) where
  appType (PPCPrimFn x) = MS.typeToCrucible (MT.typeRepr x)
  appType (PPCPrimStmt _s) = C.UnitRepr
  appType (PPCPrimTerm _t) = C.UnitRepr

instance C.PrettyApp (PPCStmtExtension v) where
  ppApp ppSub (PPCPrimFn x) =
    I.runIdentity (MC.ppArchFn (I.Identity . A.liftAtomIn ppSub) x)
  ppApp ppSub (PPCPrimStmt s) =
    MC.ppArchStmt (A.liftAtomIn ppSub) s
  ppApp _ppSub (PPCPrimTerm t) = MC.prettyF t

type instance MSB.MacawArchStmtExtension (MP.AnyPPC v) =
  PPCStmtExtension v
