{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.AArch32.Symbolic (
  aarch32MacawSymbolicFns
  , lookupReg
  , updateReg
  , AF.AArch32Exception(..)
  ) where

import qualified Data.Text as T
import           GHC.Stack ( HasCallStack )

import           Control.Lens ( (&), (%~) )
import           Control.Monad ( void )
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.State as CMS
import qualified Data.Functor.Identity as I
import           Data.Kind ( Type )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Backend as MSB
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Sequence as Seq
import qualified What4.ProgramLoc as WP
import qualified What4.Symbol as WS
import qualified What4.Utils.StringLiteral as WUS

import qualified SemMC.Architecture.AArch32 as SA
import qualified Data.Macaw.ARM.Arch as MAA
import qualified Data.Macaw.ARM.ARMReg as MAR

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Extension as CE
import qualified Lang.Crucible.CFG.Expr as LCE
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator.RegMap as MCR
import qualified Lang.Crucible.Simulator.RegValue as MCRV
import qualified Lang.Crucible.Types as CT

import qualified Data.Macaw.AArch32.Symbolic.AtomWrapper as AA
import qualified Data.Macaw.AArch32.Symbolic.Functions as AF
import qualified Data.Macaw.AArch32.Symbolic.Panic as AP
import qualified Data.Macaw.AArch32.Symbolic.Regs as AR

aarch32MacawSymbolicFns :: MS.MacawSymbolicArchFunctions SA.AArch32
aarch32MacawSymbolicFns =
  MSB.MacawSymbolicArchFunctions
  { MSB.crucGenArchConstraints = \x -> x
  , MSB.crucGenArchRegName = aarch32RegName
  , MSB.crucGenRegAssignment = AR.aarch32RegAssignment
  , MSB.crucGenRegStructType = AR.aarch32RegStructType
  , MSB.crucGenArchFn = aarch32GenFn
  , MSB.crucGenArchStmt = aarch32GenStmt
  , MSB.crucGenArchTermStmt = aarch32GenTermStmt
  }

aarch32RegName :: MAR.ARMReg tp -> WS.SolverSymbol
aarch32RegName r = WS.safeSymbol ("r!" ++ show (MC.prettyF r))

aarch32MacawEvalFn :: (CB.IsSymInterface sym)
                   => AF.SymFuns sym
                   -> MS.MacawArchStmtExtensionOverride SA.AArch32
                   -> MS.MacawArchEvalFn p sym mem SA.AArch32
aarch32MacawEvalFn fs (MS.MacawArchStmtExtensionOverride override) =
  MSB.MacawArchEvalFn $ \_ _ xt s -> do
    mRes <- override xt s
    case mRes of
      Nothing ->
        case xt of
          AArch32PrimFn p -> AF.funcSemantics fs p s
          AArch32PrimStmt p -> AF.stmtSemantics fs p s
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

instance FC.FunctorFC AArch32StmtExtension where
  fmapFC f st =
    case st of
      AArch32PrimFn p -> AArch32PrimFn (FC.fmapFC (AA.liftAtomMap f) p)
      AArch32PrimStmt p -> AArch32PrimStmt (TF.fmapF (AA.liftAtomMap f) p)

instance FC.FoldableFC AArch32StmtExtension where
  foldMapFC f st =
    case st of
      AArch32PrimFn p -> FC.foldMapFC (AA.liftAtomIn f) p
      AArch32PrimStmt p -> TF.foldMapF (AA.liftAtomIn f) p

instance FC.TraversableFC AArch32StmtExtension where
  traverseFC f st =
    case st of
      AArch32PrimFn p -> AArch32PrimFn <$> FC.traverseFC (AA.liftAtomTrav f) p
      AArch32PrimStmt p -> AArch32PrimStmt <$> TF.traverseF (AA.liftAtomTrav f) p

instance CE.TypeApp AArch32StmtExtension where
  appType st =
    case st of
      AArch32PrimFn p -> MS.typeToCrucible (MT.typeRepr p)
      AArch32PrimStmt _p -> CT.UnitRepr

instance CE.PrettyApp AArch32StmtExtension where
  ppApp ppSub st =
    case st of
      AArch32PrimFn p ->
        I.runIdentity (MC.ppArchFn (I.Identity . AA.liftAtomIn ppSub) p)
      AArch32PrimStmt p ->
        MC.ppArchStmt (AA.liftAtomIn ppSub) p

type instance MSB.MacawArchStmtExtension SA.AArch32 =
  AArch32StmtExtension

aarch32GenFn :: MAA.ARMPrimFn (MC.Value SA.AArch32 ids) tp
             -> MSB.CrucGen SA.AArch32 ids s (CR.Atom s (MS.ToCrucibleType tp))
aarch32GenFn fn =
  case fn of
    MAA.ARMSyscall _imm v0 v1 v2 v3 v4 v5 v6 v7 -> do
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
      let retTypes = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32) Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
      let retRepr = CT.StructRepr retTypes
      syscallArgStructAtom <- MSB.evalAtom (CR.EvalApp (LCE.MkStruct argTypes syscallArgs))
      let lookupHdlStmt = MS.MacawLookupSyscallHandle argTypes retTypes syscallArgStructAtom
      hdlAtom <- MSB.evalMacawStmt lookupHdlStmt
      MSB.evalAtom $! CR.Call hdlAtom syscallArgs retRepr
    _ -> do
      let f x = AA.AtomWrapper <$> MSB.valueToCrucible x
      r <- FC.traverseFC f fn
      MSB.evalArchStmt (AArch32PrimFn r)

aarch32GenStmt :: MAA.ARMStmt (MC.Value SA.AArch32 ids)
               -> MSB.CrucGen SA.AArch32 ids s ()
aarch32GenStmt s = do
  let f x = AA.AtomWrapper <$> MSB.valueToCrucible x
  s' <- TF.traverseF f s
  void (MSB.evalArchStmt (AArch32PrimStmt s'))

-- | Create labels for a conditional branch in a Crucible statement handler
--
-- Create two labels (returned in order): the True label (to take when a
-- condition evaluates to true during symbolic execution) and the False label
-- (to fall through to otherwise)
--
-- This function requires that the fallthrough label exists; if we don't have
-- one at translation time, make a fresh block that ends in an error.
--
-- Note that this lets us fail lazily (i.e., during symbolic execution and not
-- translation time), as this non-existence only matters if we reach this part
-- of the program during symbolic execution.
makeConditionalLabels
  :: (FC.TraversableFC (MSB.MacawArchStmtExtension arch))
  => Maybe (CR.Label s)
  -- ^ The fallthrough label
  -> String
  -- ^ A message to embed in case there is no fallthrough label and the block is
  -- reached during symbolic execution
  -> MSB.CrucGen arch ids s (CR.Label s, CR.Label s)
makeConditionalLabels mfallthroughLabel msg = do
  tlbl <- CR.Label <$> MSB.freshValueIndex
  flbl <- case mfallthroughLabel of
    Just ft -> return ft
    Nothing -> do
      ft <- CR.Label <$> MSB.freshValueIndex
      errMsg <- MSB.evalAtom (CR.EvalApp (LCE.StringLit (WUS.UnicodeLiteral (T.pack msg))))
      let err = CR.ErrorStmt errMsg
      let eblock = CR.mkBlock (CR.LabelID ft) mempty mempty (WP.Posd WP.InternalPos err)
      MSB.addExtraBlock eblock
      return ft
  return (tlbl, flbl)


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
    MAA.CallIf cond pc lr -> do
      cond' <- MSB.valueToCrucible cond
      pc' <- MSB.valueToCrucible pc
      lr' <- MSB.valueToCrucible lr
      callIf cond' pc' lr'
    MAA.CallIfNot cond pc lr -> do
      cond' <- MSB.valueToCrucible cond
      pc' <- MSB.valueToCrucible pc
      lr' <- MSB.valueToCrucible lr
      notc <- MSB.appAtom (LCE.Not cond')
      callIf notc pc' lr'
  where
    returnIf cond = do
      MSB.setMachineRegs =<< MSB.createRegStruct regs
      (tlbl, flbl) <- makeConditionalLabels mfallthroughLabel "No fallthrough for conditional return"

      regValues <- MSB.createRegStruct regs
      let ret = CR.Return regValues
      let rblock = CR.mkBlock (CR.LabelID tlbl) mempty mempty (WP.Posd WP.InternalPos ret)
      MSB.addExtraBlock rblock

      MSB.addTermStmt $! CR.Br cond tlbl flbl

    -- Implement the semantics of conditional calls in Crucible
    --
    -- Note that we avoid generating Crucible IR with the 'MSB.CrucGen' monad
    -- here because that adds code to the *current* block. We need to create
    -- extra blocks here to model the necessary control flow.
    callIf cond pc lr = do

      -- First, create two labels: the True label (to take when @cond@ is true
      -- during symbolic execution) and the False label (to fall through to
      -- otherwise)
      (tlbl, flbl) <- makeConditionalLabels mfallthroughLabel "No fallthrough for conditional call"

      archFns <- CMS.gets MSB.translateFns
      regsReg <- CMS.gets MSB.crucRegisterReg
      let tps = MS.typeCtxToCrucible $ FC.fmapFC MT.typeRepr $ MS.crucGenRegAssignment archFns
      let regsType = CT.StructRepr tps

      -- Next, make a block to issue the call. We need to snapshot the register
      -- state, pass it to the function handle lookup, then pass the snapshot
      -- state to the actual function call, and then finally put the state back.
      --
      -- Note that we need to poke in the actual PC and LR values that are
      -- active when we take the conditional call.  In the natural register
      -- state at this point, the PC and LR contain muxes, with the actual
      -- values taken depending on what the condition evaluates to. They are
      -- correct as muxes, but if we leave them as muxes, the function that
      -- looks them up might not handle that well. Some clients do not handle
      -- symbolic function pointers, even when they resolve to a trivially
      -- concrete value under the path condition. To account for that, in the
      -- case where the conditional call is taken, we poke in the resolved PC
      -- and LR to strip off the mux. Note that they could still be symbolic.
      fhAtom <- MSB.mkAtom (CT.FunctionHandleRepr (Ctx.singleton regsType) regsType)
      initialRegsAtom <- MSB.mkAtom regsType
      pcRegsAtom <- MSB.mkAtom regsType
      lrRegsAtom <- MSB.mkAtom regsType
      newRegsAtom <- MSB.mkAtom regsType

      let pcIdx = MSB.crucibleIndex (indexForReg MC.ip_reg)
      let lrIdx = MSB.crucibleIndex (indexForReg MAR.lr)

      let stmts = [ CR.DefineAtom initialRegsAtom $ CR.ReadReg regsReg
                  , CR.DefineAtom pcRegsAtom $ CR.EvalApp $ LCE.SetStruct tps initialRegsAtom pcIdx pc
                  , CR.DefineAtom lrRegsAtom $ CR.EvalApp $ LCE.SetStruct tps pcRegsAtom lrIdx lr
                  , CR.DefineAtom fhAtom $ CR.EvalExt (MS.MacawLookupFunctionHandle (MS.crucArchRegTypes archFns) lrRegsAtom)
                  , CR.DefineAtom newRegsAtom $ CR.Call fhAtom (Ctx.singleton lrRegsAtom) regsType
                  , CR.SetReg regsReg newRegsAtom
                  ]
      let asInternal = WP.Posd WP.InternalPos
      let callBlock = CR.mkBlock (CR.LabelID tlbl) mempty (Seq.fromList [ asInternal s | s <- stmts]) (WP.Posd WP.InternalPos (CR.Jump flbl))
      MSB.addExtraBlock callBlock

      -- Finally, jump to either the block with the call or the fallthrough
      -- label to skip it
      MSB.addTermStmt $! CR.Br cond tlbl flbl


regIndexMap :: MSB.RegIndexMap SA.AArch32
regIndexMap = MSB.mkRegIndexMap asgn sz
  where
    asgn = AR.aarch32RegAssignment
    sz = Ctx.size (MS.typeCtxToCrucible (FC.fmapFC MT.typeRepr asgn))

indexForReg
  :: (HasCallStack)
  => MAR.ARMReg tp
  -> MSB.IndexPair (MS.ArchRegContext SA.AArch32) tp
indexForReg reg =
  case MapF.lookup reg regIndexMap of
    Nothing -> AP.panic AP.AArch32 "indexForReg" ["Missing register index mapping for register: " ++ show reg]
    Just p -> p

updateReg :: (HasCallStack)
          => MAR.ARMReg tp
          -> (f (MS.ToCrucibleType tp) -> f (MS.ToCrucibleType tp))
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes SA.AArch32)
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes SA.AArch32)
updateReg reg upd asgn =
  asgn & MapF.ixF (MSB.crucibleIndex (indexForReg reg)) %~ upd

aarch32UpdateReg :: MCR.RegEntry sym (MS.ArchRegStruct SA.AArch32)
                 -> MAR.ARMReg tp
                 -> MCRV.RegValue sym (MS.ToCrucibleType tp)
                 -> MCR.RegEntry sym (MS.ArchRegStruct SA.AArch32)
aarch32UpdateReg regs reg val =
  regs { MCR.regValue = updateReg reg (const (MCRV.RV val)) (MCR.regValue regs) }

lookupReg :: (HasCallStack)
          => MAR.ARMReg tp
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes SA.AArch32)
          -> f (MS.ToCrucibleType tp)
lookupReg reg regs =
  regs Ctx.! MSB.crucibleIndex (indexForReg reg)

aarch32LookupReg :: MCR.RegEntry sym (MS.ArchRegStruct SA.AArch32)
                 -> MAR.ARMReg tp
                 -> MCR.RegEntry sym (MS.ToCrucibleType tp)
aarch32LookupReg regs reg =
  case lookupReg reg (MCR.regValue regs) of
    MCRV.RV val -> MCR.RegEntry (MS.typeToCrucible (MT.typeRepr reg)) val
