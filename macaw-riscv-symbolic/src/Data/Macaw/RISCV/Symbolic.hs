{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Macaw.RISCV.Symbolic
  ( riscvMacawSymbolicFns
  , riscvMacawEvalFn
  , lookupReg
  , updateReg
  ) where

import Control.Lens ((%~), (&))
import qualified Control.Monad.Catch as X
import Control.Monad.IO.Class (liftIO)
import Data.Functor (void)
import qualified Data.Kind as DK
import qualified Data.Functor.Identity as I
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as FC
import Data.Typeable (Typeable)

-- crucible
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.Types as C

-- crucible-llvm
import qualified Lang.Crucible.LLVM.MemModel as LCLM

-- grift
import qualified GRIFT.Types as G

-- what4
import qualified What4.Symbol as WS

-- macaw-base
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT

-- macaw-riscv
import qualified Data.Macaw.RISCV as MR

-- macaw-symbolic
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Backend as MSB

-- macaw-riscv-symbolic
import qualified Data.Macaw.RISCV.Symbolic.AtomWrapper as RA
import qualified Data.Macaw.RISCV.Symbolic.Functions as RF
import qualified Data.Macaw.RISCV.Symbolic.Repeat as RR

riscvMacawSymbolicFns ::
     forall rv
   . (G.KnownRV rv, MR.RISCVConstraints rv)
  => MS.MacawSymbolicArchFunctions (MR.RISCV rv)
riscvMacawSymbolicFns =
  MSB.MacawSymbolicArchFunctions
  { MSB.crucGenArchConstraints = \x -> x
  , MSB.crucGenArchRegName = riscvRegName
  , MSB.crucGenRegAssignment = riscvRegAssignment
  , MSB.crucGenRegStructType = riscvRegStructType (PC.knownRepr :: G.RVRepr rv)
  , MSB.crucGenArchFn = riscvGenFn
  , MSB.crucGenArchStmt = riscvGenStmt
  , MSB.crucGenArchTermStmt = riscvGenTermStmt
  }

type instance MS.ArchRegContext (MR.RISCV rv) =
          (Ctx.EmptyCtx Ctx.::> MT.BVType (G.RVWidth rv)  -- PC
  Ctx.<+> RR.CtxRepeat 31 (MT.BVType (G.RVWidth rv))      -- GPR regs. We use 31 instead of 32
                                                          -- because we exclude x0, which is
                                                          -- hardwired to the constant 0.
  Ctx.<+> RR.CtxRepeat 32 (MT.BVType (G.RVFloatWidth rv)) -- FPR regs
  Ctx.<+> RR.CtxRepeat 23 (MT.BVType (G.RVWidth rv))      -- CSR regs. Although there is a
                                                          -- theoretical maximum of 4096 of
                                                          -- these registers, `grift` only
                                                          -- supports 23 of them in practice.
  Ctx.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 2               -- PrivLevel
                        Ctx.::> MT.BoolType))             -- EXC

riscvMacawEvalFn :: RF.SymFuns sym
                 -> MS.MacawArchStmtExtensionOverride (MR.RISCV rv)
                 -> MS.MacawArchEvalFn p sym mem (MR.RISCV rv)
riscvMacawEvalFn fs (MS.MacawArchStmtExtensionOverride override) =
  MSB.MacawArchEvalFn $ \_ _ xt s -> do
    mRes <- override xt s
    case mRes of
      Nothing ->
        case xt of
          RISCVPrimFn fn -> RF.funcSemantics fs fn s
          RISCVPrimStmt stmt -> RF.stmtSemantics fs stmt s
          RISCVPrimTerm term -> RF.termSemantics fs term s
      Just res -> return res

instance (MS.IsMemoryModel mem, G.KnownRV rv, MR.RISCVConstraints rv, Typeable rv)
    => MS.GenArchInfo mem (MR.RISCV rv) where
  genArchVals _ _ mOverride = Just $ MS.GenArchVals
    { MS.archFunctions = riscvMacawSymbolicFns
    , MS.withArchEval = \sym k -> do
        sfns <- liftIO $ RF.newSymFuns sym
        let override = case mOverride of
                         Nothing -> MS.defaultMacawArchStmtExtensionOverride
                         Just ov -> ov
        k (riscvMacawEvalFn sfns override)
    , MS.withArchConstraints = \x -> x
    , MS.lookupReg = archLookupReg
    , MS.updateReg = archUpdateReg
    }

riscvRegName :: MR.RISCVReg rv tp -> WS.SolverSymbol
riscvRegName r = WS.systemSymbol ("r!" ++ show (MC.prettyF r))

-- Note that `repeatAssign` starts indexing from 0, but we want to exclude
-- `GPR 0` (i.e., x0), as this is always hardwired to the constant 0. As such,
-- we offset all of the indexes by one using (+ 1).
gprRegs :: Ctx.Assignment (MR.RISCVReg rv) (RR.CtxRepeat 31 (MT.BVType (G.RVWidth rv)))
gprRegs = RR.repeatAssign (MR.GPR . fromIntegral . (+ 1))

fprRegs :: Ctx.Assignment (MR.RISCVReg rv) (RR.CtxRepeat 32 (MT.BVType (G.RVFloatWidth rv)))
fprRegs = RR.repeatAssign (MR.FPR . fromIntegral)

-- | The RISC-V control/status registers that are directly supported by Macaw.
csrRegs :: Ctx.Assignment (MR.RISCVReg rv) (RR.CtxRepeat 23 (MT.BVType (G.RVWidth rv)))
csrRegs = RR.repeatAssign (MR.CSR . toEnum)

-- | This contains an assignment that stores the register associated with each index in the
-- RISC-V register structure.
riscvRegAssignment :: Ctx.Assignment (MR.RISCVReg rv) (MS.ArchRegContext (MR.RISCV rv))
riscvRegAssignment =
  Ctx.Empty Ctx.:> MR.PC
  Ctx.<++> gprRegs
  Ctx.<++> fprRegs
  Ctx.<++> csrRegs
  Ctx.<++> (Ctx.Empty Ctx.:> MR.PrivLevel Ctx.:> MR.EXC)

riscvRegStructType ::
     forall rv
   . G.KnownRV rv
  => G.RVRepr rv
  -> C.TypeRepr (MSB.ArchRegStruct (MR.RISCV rv))
riscvRegStructType _rv =
  C.StructRepr $ MS.typeCtxToCrucible $ FC.fmapFC MT.typeRepr $ riscvRegAssignment @rv

regIndexMap :: forall rv
             . G.KnownRV rv
            => MSB.RegIndexMap (MR.RISCV rv)
regIndexMap = MSB.mkRegIndexMap assgn sz
  where
    assgn = riscvRegAssignment @rv
    sz = Ctx.size $ MS.typeCtxToCrucible $ FC.fmapFC MT.typeRepr assgn

lookupReg :: forall rv m f tp
           . (G.KnownRV rv, Typeable rv, X.MonadThrow m)
          => MR.RISCVReg rv tp
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes (MR.RISCV rv))
          -> m (f (MS.ToCrucibleType tp))
lookupReg r asgn =
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn Ctx.! MSB.crucibleIndex pair)

archLookupReg :: (G.KnownRV rv, Typeable rv)
              => C.RegEntry sym (MS.ArchRegStruct (MR.RISCV rv))
              -> MR.RISCVReg rv tp
              -> C.RegEntry sym (MS.ToCrucibleType tp)
archLookupReg regEntry reg =
  case lookupReg reg (C.regValue regEntry) of
    Just (C.RV val) -> C.RegEntry (MS.typeToCrucible $ MT.typeRepr reg) val
    Nothing -> error $ "unexpected register: " ++ show (MC.prettyF reg)

updateReg :: forall rv m f tp
           . (G.KnownRV rv, Typeable rv, X.MonadThrow m)
          => MR.RISCVReg rv tp
          -> (f (MS.ToCrucibleType tp) -> f (MS.ToCrucibleType tp))
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes (MR.RISCV rv))
          -> m (Ctx.Assignment f (MS.MacawCrucibleRegTypes (MR.RISCV rv)))
updateReg r upd asgn = do
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn & MapF.ixF (MSB.crucibleIndex pair) %~ upd)

archUpdateReg :: (G.KnownRV rv, Typeable rv)
              => C.RegEntry sym (MS.ArchRegStruct (MR.RISCV rv))
              -> MR.RISCVReg rv tp
              -> C.RegValue sym (MS.ToCrucibleType tp)
              -> C.RegEntry sym (MS.ArchRegStruct (MR.RISCV rv))
archUpdateReg regEntry reg val =
  case updateReg reg (const $ C.RV val) (C.regValue regEntry) of
    Just r -> regEntry { C.regValue = r }
    Nothing -> error $ "unexpected register: " ++ show (MC.prettyF reg)

newtype RISCVSymbolicException rv = MissingRegisterInState (Some (MR.RISCVReg rv))
  deriving Show
instance Typeable rv => X.Exception (RISCVSymbolicException rv)

data RISCVStmtExtension rv (f :: C.CrucibleType -> DK.Type) (ctp :: C.CrucibleType) where
  -- | Wrappers around the arch-specific functions in RISC-V; these are
  -- interpreted in 'funcSemantics'.
  RISCVPrimFn :: MR.RISCVPrimFn rv (RA.AtomWrapper f) t
              -> RISCVStmtExtension rv f (MS.ToCrucibleType t)
  -- | Wrappers around the arch-specific statements in RISC-V; these are
  -- interpreted in 'stmtSemantics'
  RISCVPrimStmt :: MR.RISCVStmt rv (RA.AtomWrapper f)
                -> RISCVStmtExtension rv f C.UnitType
  -- | Wrappers around the arch-specific terminators in RISC-V; these are
  -- interpreted in 'termSemantics'
  RISCVPrimTerm :: MR.RISCVTermStmt rv (RA.AtomWrapper f)
                -> RISCVStmtExtension rv f C.UnitType

instance FC.FunctorFC (RISCVStmtExtension ppc) where
  fmapFC f (RISCVPrimFn x) = RISCVPrimFn (FC.fmapFC (RA.liftAtomMap f) x)
  fmapFC f (RISCVPrimStmt s) = RISCVPrimStmt (TF.fmapF (RA.liftAtomMap f) s)
  fmapFC f (RISCVPrimTerm t) = RISCVPrimTerm (TF.fmapF (RA.liftAtomMap f) t)

instance FC.FoldableFC (RISCVStmtExtension ppc) where
  foldMapFC f (RISCVPrimFn x) = FC.foldMapFC (RA.liftAtomIn f) x
  foldMapFC f (RISCVPrimStmt s) = TF.foldMapF (RA.liftAtomIn f) s
  foldMapFC f (RISCVPrimTerm t) = TF.foldMapF (RA.liftAtomIn f) t

instance FC.TraversableFC (RISCVStmtExtension ppc) where
  traverseFC f (RISCVPrimFn x) = RISCVPrimFn <$> FC.traverseFC (RA.liftAtomTrav f) x
  traverseFC f (RISCVPrimStmt s) = RISCVPrimStmt <$> TF.traverseF (RA.liftAtomTrav f) s
  traverseFC f (RISCVPrimTerm t) = RISCVPrimTerm <$> TF.traverseF (RA.liftAtomTrav f) t

instance C.TypeApp (RISCVStmtExtension v) where
  appType (RISCVPrimFn x) = MS.typeToCrucible (MT.typeRepr x)
  appType (RISCVPrimStmt _s) = C.UnitRepr
  appType (RISCVPrimTerm _t) = C.UnitRepr

instance C.PrettyApp (RISCVStmtExtension v) where
  ppApp ppSub (RISCVPrimFn x) =
    I.runIdentity (MC.ppArchFn (I.Identity . RA.liftAtomIn ppSub) x)
  ppApp ppSub (RISCVPrimStmt s) =
    MC.ppArchStmt (RA.liftAtomIn ppSub) s
  ppApp ppSub (RISCVPrimTerm t) = MC.ppArchTermStmt (RA.liftAtomIn ppSub) t

type instance MSB.MacawArchStmtExtension (MR.RISCV rv) = RISCVStmtExtension rv

riscvGenFn :: forall rv ids s tp
            . MR.RISCVPrimFn rv (MC.Value (MR.RISCV rv) ids) tp
           -> MSB.CrucGen (MR.RISCV rv) ids s (C.Atom s (MS.ToCrucibleType tp))
riscvGenFn fn =
  case fn of
    MR.RISCVEcall w v0 v1 v2 v3 v4 v5 v6 v7 -> do
      a0 <- MSB.valueToCrucible v0
      a1 <- MSB.valueToCrucible v1
      a2 <- MSB.valueToCrucible v2
      a3 <- MSB.valueToCrucible v3
      a4 <- MSB.valueToCrucible v4
      a5 <- MSB.valueToCrucible v5
      a6 <- MSB.valueToCrucible v6
      a7 <- MSB.valueToCrucible v7

      let syscallArgs = Ctx.Empty Ctx.:> a0 Ctx.:> a1 Ctx.:> a2 Ctx.:> a3 Ctx.:> a4 Ctx.:> a5 Ctx.:> a6 Ctx.:> a7
      let argTypes = PC.knownRepr
      let retTypes = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr w Ctx.:> LCLM.LLVMPointerRepr w
      let retRepr = C.StructRepr retTypes
      syscallArgStructAtom <- MSB.evalAtom (C.EvalApp (C.MkStruct argTypes syscallArgs))
      let lookupHdlStmt = MS.MacawLookupSyscallHandle argTypes retTypes syscallArgStructAtom
      hdlAtom <- MSB.evalMacawStmt lookupHdlStmt
      MSB.evalAtom $! C.Call hdlAtom syscallArgs retRepr

riscvGenStmt :: forall rv ids s
              . MR.RISCVStmt rv (MC.Value (MR.RISCV rv) ids)
             -> MSB.CrucGen (MR.RISCV rv) ids s ()
riscvGenStmt s = do
  s' <- TF.traverseF f s
  void (MSB.evalArchStmt (RISCVPrimStmt s'))
  where
    f :: forall a
       . MC.Value (MR.RISCV rv) ids a
      -> MSB.CrucGen (MR.RISCV rv) ids s (RA.AtomWrapper (C.Atom s) a)
    f x = RA.AtomWrapper <$> MSB.valueToCrucible x

riscvGenTermStmt :: forall rv ids s
                  . MR.RISCVTermStmt rv (MC.Value (MR.RISCV rv) ids)
                 -> MC.RegState (MR.RISCVReg rv) (MC.Value (MR.RISCV rv) ids)
                 -> Maybe (C.Label s)
                 -> MSB.CrucGen (MR.RISCV rv) ids s ()
riscvGenTermStmt ts _rs _fallthrough = do
  ts' <- TF.traverseF f ts
  void (MSB.evalArchStmt (RISCVPrimTerm ts'))
  where
    f :: forall a
       . MC.Value (MR.RISCV rv) ids a
      -> MSB.CrucGen (MR.RISCV rv) ids s (RA.AtomWrapper (C.Atom s) a)
    f x = RA.AtomWrapper <$> MSB.valueToCrucible x
