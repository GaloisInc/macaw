{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.AArch32.Symbolic (
  aarch32MacawSymbolicFns
  , lookupReg
  , updateReg
  ) where

import qualified Data.Text as T
import           GHC.TypeLits

import           Control.Lens ( (&), (%~) )
import           Control.Monad ( void )
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.Functor.Identity as I
import           Data.Kind ( Type )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Backend as MSB
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.CtxFuns as PC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy ( Proxy(..) )
import qualified What4.BaseTypes as WT
import qualified What4.ProgramLoc as WP
import qualified What4.Utils.StringLiteral as WUS
import qualified What4.Symbol as WS

import qualified Language.ASL.Globals as LAG
import qualified SemMC.Architecture.AArch32 as SA
import qualified Data.Macaw.ARM.Arch as MAA
import qualified Data.Macaw.ARM.ARMReg as MAR

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Extension as CE
import qualified Lang.Crucible.CFG.Expr as LCE
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.Simulator.RegMap as MCR
import qualified Lang.Crucible.Simulator.RegValue as MCRV
import qualified Lang.Crucible.Types as CT

import qualified Data.Macaw.AArch32.Symbolic.AtomWrapper as AA
import qualified Data.Macaw.AArch32.Symbolic.Functions as AF
import qualified Data.Macaw.AArch32.Symbolic.Panic as AP

aarch32MacawSymbolicFns :: MS.MacawSymbolicArchFunctions SA.AArch32
aarch32MacawSymbolicFns =
  MSB.MacawSymbolicArchFunctions
  { MSB.crucGenArchConstraints = \x -> x
  , MSB.crucGenArchRegName = aarch32RegName
  , MSB.crucGenRegAssignment = aarch32RegAssignment
  , MSB.crucGenRegStructType = aarch32RegStructType
  , MSB.crucGenArchFn = aarch32GenFn
  , MSB.crucGenArchStmt = aarch32GenStmt
  , MSB.crucGenArchTermStmt = aarch32GenTermStmt
  }

aarch32RegName :: MAR.ARMReg tp -> WS.SolverSymbol
aarch32RegName r = WS.safeSymbol ("r!" ++ show (MC.prettyF r))

aarch32MacawEvalFn :: (CB.IsSymInterface sym)
                   => AF.SymFuns sym
                   -> MS.MacawArchStmtExtensionOverride SA.AArch32
                   -> MS.MacawArchEvalFn sym mem SA.AArch32
aarch32MacawEvalFn fs (MS.MacawArchStmtExtensionOverride override) =
  MSB.MacawArchEvalFn $ \_ _ xt s -> do
    mRes <- override xt s
    case mRes of
      Nothing ->
        case xt of
          AArch32PrimFn p -> AF.funcSemantics fs p s
          AArch32PrimStmt p -> AF.stmtSemantics fs p s
          AArch32PrimTerm p -> AF.termSemantics fs p s
      Just res -> return res

instance MS.GenArchInfo mem SA.AArch32 where
  genArchVals _ _ mOverride = Just $ MS.GenArchVals
                    { MS.archFunctions = aarch32MacawSymbolicFns
                    , MS.withArchEval = \sym k -> do
                        sfns <- liftIO $ AF.newSymFuns sym
                        let override = case mOverride of
                                         Nothing -> MS.defaultMacawArchStmtExtensionOverride
                                         Just ov -> ov
                        k (aarch32MacawEvalFn sfns override)
                    , MS.withArchConstraints = \x -> x
                    , MS.lookupReg = aarch32LookupReg
                    , MS.updateReg = aarch32UpdateReg
                    }

data AArch32StmtExtension (f :: CT.CrucibleType -> Type) (ctp :: CT.CrucibleType) where
  AArch32PrimFn :: MAA.ARMPrimFn (AA.AtomWrapper f) t -> AArch32StmtExtension f (MS.ToCrucibleType t)
  AArch32PrimStmt :: MAA.ARMStmt (AA.AtomWrapper f) -> AArch32StmtExtension f CT.UnitType
  AArch32PrimTerm :: MAA.ARMTermStmt (AA.AtomWrapper f) -> AArch32StmtExtension f CT.UnitType

instance FC.FunctorFC AArch32StmtExtension where
  fmapFC f st =
    case st of
      AArch32PrimFn p -> AArch32PrimFn (FC.fmapFC (AA.liftAtomMap f) p)
      AArch32PrimStmt p -> AArch32PrimStmt (TF.fmapF (AA.liftAtomMap f) p)
      AArch32PrimTerm p -> AArch32PrimTerm (TF.fmapF (AA.liftAtomMap f) p)

instance FC.FoldableFC AArch32StmtExtension where
  foldMapFC f st =
    case st of
      AArch32PrimFn p -> FC.foldMapFC (AA.liftAtomIn f) p
      AArch32PrimStmt p -> TF.foldMapF (AA.liftAtomIn f) p
      AArch32PrimTerm p -> TF.foldMapF (AA.liftAtomIn f) p

instance FC.TraversableFC AArch32StmtExtension where
  traverseFC f st =
    case st of
      AArch32PrimFn p -> AArch32PrimFn <$> FC.traverseFC (AA.liftAtomTrav f) p
      AArch32PrimStmt p -> AArch32PrimStmt <$> TF.traverseF (AA.liftAtomTrav f) p
      AArch32PrimTerm p -> AArch32PrimTerm <$> TF.traverseF (AA.liftAtomTrav f) p

instance CE.TypeApp AArch32StmtExtension where
  appType st =
    case st of
      AArch32PrimFn p -> MS.typeToCrucible (MT.typeRepr p)
      AArch32PrimStmt _p -> CT.UnitRepr
      AArch32PrimTerm _p -> CT.UnitRepr

instance CE.PrettyApp AArch32StmtExtension where
  ppApp ppSub st =
    case st of
      AArch32PrimFn p ->
        I.runIdentity (MC.ppArchFn (I.Identity . AA.liftAtomIn ppSub) p)
      AArch32PrimStmt p ->
        MC.ppArchStmt (AA.liftAtomIn ppSub) p
      AArch32PrimTerm p -> MC.ppArchTermStmt (AA.liftAtomIn ppSub) p

type instance MSB.MacawArchStmtExtension SA.AArch32 =
  AArch32StmtExtension

-- | All of the registers tracked in the AArch32 machine code model
--
-- Note that this set is significantly larger than the user-visible
-- architectural state and includes a large number of hidden state from the ASL
-- semantics
--
-- See Note [ARM Registers]
type RegContext = PC.MapCtx ToMacawTypeWrapper (LAG.SimpleGlobalsCtx Ctx.<+> LAG.GPRCtx Ctx.<+> LAG.SIMDCtx)
type instance MS.ArchRegContext SA.AArch32 = RegContext

data ToMacawTypeWrapper :: PC.TyFun WT.BaseType MT.Type -> Type
type instance PC.Apply ToMacawTypeWrapper t = BaseToMacawType t

aarch32RegAssignment :: Ctx.Assignment MAR.ARMReg RegContext
aarch32RegAssignment =
  I.runIdentity (PC.traverseMapCtx (Proxy @AsMacawReg) asARMReg (FC.fmapFC LAG.SimpleGlobalRef LAG.simpleGlobalRefs Ctx.<++> LAG.gprGlobalRefsSym Ctx.<++> LAG.simdGlobalRefsSym))

data AsMacawReg :: PC.TyFun Symbol MT.Type -> Type
type instance PC.Apply AsMacawReg s = BaseToMacawType (LAG.GlobalsType s)

asARMReg :: (Monad m) => LAG.GlobalRef s -> m (MAR.ARMReg (BaseToMacawType (LAG.GlobalsType s)))
asARMReg gr =
  case LAG.globalRefRepr gr of
    WT.BaseBoolRepr -> return (MAR.ARMGlobalBool gr)
    WT.BaseBVRepr _ -> return (MAR.ARMGlobalBV gr)
    WT.BaseStructRepr Ctx.Empty -> return MAR.ARMDummyReg
    tp -> AP.panic AP.AArch32 "asARMReg" ["Unexpected type: " ++ show tp]

type family BaseToMacawType (t :: WT.BaseType) :: MT.Type where
  BaseToMacawType WT.BaseBoolType = MT.BoolType
  BaseToMacawType (WT.BaseBVType n) = MT.BVType n
  BaseToMacawType (WT.BaseStructType Ctx.EmptyCtx) = MT.TupleType '[]

aarch32RegStructType :: CT.TypeRepr (MS.ArchRegStruct SA.AArch32)
aarch32RegStructType =
  CT.StructRepr (MS.typeCtxToCrucible (FC.fmapFC MT.typeRepr aarch32RegAssignment))

aarch32GenFn :: MAA.ARMPrimFn (MC.Value SA.AArch32 ids) tp
             -> MSB.CrucGen SA.AArch32 ids s (CR.Atom s (MS.ToCrucibleType tp))
aarch32GenFn fn = do
  let f x = AA.AtomWrapper <$> MSB.valueToCrucible x
  r <- FC.traverseFC f fn
  MSB.evalArchStmt (AArch32PrimFn r)

aarch32GenStmt :: MAA.ARMStmt (MC.Value SA.AArch32 ids)
               -> MSB.CrucGen SA.AArch32 ids s ()
aarch32GenStmt s = do
  let f x = AA.AtomWrapper <$> MSB.valueToCrucible x
  s' <- TF.traverseF f s
  void (MSB.evalArchStmt (AArch32PrimStmt s'))

aarch32GenTermStmt :: MAA.ARMTermStmt (MC.Value SA.AArch32 ids)
                   -> MC.RegState MAR.ARMReg (MC.Value SA.AArch32 ids)
                   -> Maybe (CR.Label s)
                   -> MSB.CrucGen SA.AArch32 ids s ()
aarch32GenTermStmt ts regs mfallthroughLabel =
  case ts of
    MAA.ReturnIf cond -> returnIf =<< MSB.valueToCrucible cond
    MAA.ReturnIfNot cond -> do
      notc <- MSB.appAtom =<< LCE.Not <$> MSB.valueToCrucible cond
      returnIf notc
    _ -> do
      ts' <- TF.traverseF f ts
      void (MSB.evalArchStmt (AArch32PrimTerm ts'))
  where
    f x = AA.AtomWrapper <$> MSB.valueToCrucible x
    returnIf cond = do
      MSB.setMachineRegs =<< MSB.createRegStruct regs
      tlbl <- CR.Label <$> MSB.freshValueIndex
      flbl <- case mfallthroughLabel of
        Just ft -> return ft
        Nothing -> do
          ft <- CR.Label <$> MSB.freshValueIndex
          errMsg <- MSB.evalAtom (CR.EvalApp (LCE.StringLit (WUS.UnicodeLiteral (T.pack "No fallthrough for conditional return"))))
          let err = CR.ErrorStmt errMsg
          let eblock = CR.mkBlock (CR.LabelID ft) mempty mempty (WP.Posd WP.InternalPos err)
          MSB.addExtraBlock eblock
          return ft

      regValues <- MSB.createRegStruct regs
      let ret = CR.Return regValues
      let rblock = CR.mkBlock (CR.LabelID tlbl) mempty mempty (WP.Posd WP.InternalPos ret)
      MSB.addExtraBlock rblock

      MSB.addTermStmt $! CR.Br cond tlbl flbl

regIndexMap :: MSB.RegIndexMap SA.AArch32
regIndexMap = MSB.mkRegIndexMap asgn sz
  where
    asgn = aarch32RegAssignment
    sz = Ctx.size (MS.typeCtxToCrucible (FC.fmapFC MT.typeRepr asgn))

updateReg :: MAR.ARMReg tp
          -> (f (MS.ToCrucibleType tp) -> f (MS.ToCrucibleType tp))
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes SA.AArch32)
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes SA.AArch32)
updateReg reg upd asgn =
  case MapF.lookup reg regIndexMap of
    Just pair -> asgn & MapF.ixF (MSB.crucibleIndex pair) %~ upd
    Nothing -> AP.panic AP.AArch32 "updateReg" ["Missing reg entry for register: " ++ show reg]

aarch32UpdateReg :: MCR.RegEntry sym (MS.ArchRegStruct SA.AArch32)
                 -> MAR.ARMReg tp
                 -> MCRV.RegValue sym (MS.ToCrucibleType tp)
                 -> MCR.RegEntry sym (MS.ArchRegStruct SA.AArch32)
aarch32UpdateReg regs reg val =
  regs { MCR.regValue = updateReg reg (const (MCRV.RV val)) (MCR.regValue regs) }

lookupReg :: MAR.ARMReg tp
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes SA.AArch32)
          -> f (MS.ToCrucibleType tp)
lookupReg reg regs =
  case MapF.lookup reg regIndexMap of
    Just pair -> regs Ctx.! MSB.crucibleIndex pair
    Nothing -> AP.panic AP.AArch32 "lookupReg" ["Missing reg entry for register: " ++ show reg]

aarch32LookupReg :: MCR.RegEntry sym (MS.ArchRegStruct SA.AArch32)
                 -> MAR.ARMReg tp
                 -> MCR.RegEntry sym (MS.ToCrucibleType tp)
aarch32LookupReg regs reg =
  case lookupReg reg (MCR.regValue regs) of
    MCRV.RV val -> MCR.RegEntry (MS.typeToCrucible (MT.typeRepr reg)) val

{- Note [ARM Registers]

The symbolic execution (and the code discovery in macaw-aarch32) track a
superset of the user-visible architectural state, which only includes the GPRs
and SIMD registers.  The extended state includes low-level architectural details
referenced by the ASL semantics.

In asl-translator, the set of architectural state is referred to as the
"tracked" registers (or allGlobalRefs).  This is state that must be maintained
during code discovery and symbolic execution, which includes things like:

- The IT state
- Branch taken/not taken flags
- Various flags

Note that there are "untracked" state, which is architectural state referred to
in the semantics, but that is entirely local to an instruction.  These are
equivalent to local variables and do not appear in the post states of any
instructions.  We do not track those in the symbolic execution because they are
effectively inlined when we symbolically execute the ASL semantics into formulas
for semmc.

-}
