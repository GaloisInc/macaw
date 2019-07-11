-- This module is currently unused; it models certain functions we are generating via
-- template haskell, but these functions aren't actually used themselves.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.PPC.Semantics.Base
  ( crucAppToExpr
  , locToReg
  , interpretFormula
  ) where

import qualified Data.Foldable as F
import           Data.Proxy
import           GHC.TypeLits

import           Data.Parameterized.Classes
import qualified What4.BaseTypes as S
import qualified What4.Expr.BoolMap as BooM
import qualified What4.Expr.Builder as S
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.InterpretedFloatingPoint as SFP
import qualified What4.SemiRing as SR

import qualified SemMC.Architecture.PPC as SP
import qualified SemMC.Architecture.PPC.Location as APPC
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.Symbolic as MS

import Data.Parameterized.NatRepr ( knownNat
                                  , addNat
                                  , intValue
                                  , natValue
                                  )

import           Data.Macaw.SemMC.Generator
import           Data.Macaw.PPC.Arch ( PPCArchConstraints )
import           Data.Macaw.PPC.PPCReg

type family FromCrucibleBaseType (btp :: S.BaseType) :: M.Type where
  FromCrucibleBaseType (S.BaseBVType w) = M.BVType w
  FromCrucibleBaseType (S.BaseBoolType) = M.BoolType
  FromCrucibleBaseType (S.BaseFloatType fpp) =
    M.FloatType (MS.FromCrucibleFloatInfo (SFP.FloatPrecisionToInfo fpp))

crucAppToExpr :: (M.ArchConstraints ppc) =>
                 S.App (S.Expr t) ctp
              -> Generator ppc ids s (Expr ppc ids (FromCrucibleBaseType ctp))
crucAppToExpr (S.NotPred bool) = AppExpr . M.NotApp <$> addElt bool
crucAppToExpr (S.ConjPred boolmap) = evalBoolMap AndOp True boolmap
crucAppToExpr (S.DisjPred boolmap) = evalBoolMap OrOp False boolmap
crucAppToExpr (S.BaseIte bt _ test t f) = AppExpr <$>
  case bt of
    S.BaseBoolRepr ->
      M.Mux <$> pure M.BoolTypeRepr <*> addElt test <*> addElt t <*> addElt f
    S.BaseBVRepr w ->
      M.Mux <$> pure (M.BVTypeRepr w) <*> addElt test <*> addElt t <*> addElt f
    S.BaseFloatRepr fpp ->
      M.Mux
      (M.FloatTypeRepr (MS.floatInfoFromCrucible $ SFP.floatPrecisionToInfoRepr fpp))
      <$> addElt test <*> addElt t <*> addElt f
    _ -> error "unsupported BaseITE repr for macaw PPC base semantics"
crucAppToExpr (S.BaseEq _bt bv1 bv2) =
  AppExpr <$> do M.Eq <$> addElt bv1 <*> addElt bv2

crucAppToExpr (S.BVSlt bv1 bv2) = AppExpr <$> do
  M.BVSignedLt <$> addElt bv1 <*> addElt bv2
crucAppToExpr (S.BVUlt bv1 bv2) = AppExpr <$> do
  M.BVUnsignedLt <$> addElt bv1 <*> addElt bv2
crucAppToExpr (S.BVConcat w bv1 bv2) = AppExpr <$> do
  let u = S.bvWidth bv1
      v = S.bvWidth bv2
  bv1Val <- addElt bv1
  bv2Val <- addElt bv2
  S.LeqProof <- return $ S.leqAdd2 (S.leqRefl u) (S.leqProof (knownNat @1) v)
  pf1@S.LeqProof <- return $ S.leqAdd2 (S.leqRefl v) (S.leqProof (knownNat @1) u)
  Refl <- return $ S.plusComm u v
  S.LeqProof <- return $ S.leqTrans pf1 (S.leqRefl w)
  bv1Ext <- addExpr (AppExpr (M.UExt bv1Val w)) ---(u `addNat` v)))
  bv2Ext <- addExpr (AppExpr (M.UExt bv2Val w))
  bv1Shifter <- addExpr (ValueExpr (M.BVValue w (intValue v)))
  bv1Shf <- addExpr (AppExpr (M.BVShl w bv1Ext bv1Shifter))
  return $ M.BVOr w bv1Shf bv2Ext
crucAppToExpr (S.BVSelect idx n bv) = do
  let w = S.bvWidth bv
  bvVal <- addElt bv
  case natValue n + 1 <= natValue w of
    True -> do
      -- Is there a way to just "know" that n + 1 <= w?
      Just S.LeqProof <- return $ S.testLeq (n `addNat` (knownNat @1)) w
      pf1@S.LeqProof <- return $ S.leqAdd2 (S.leqRefl idx) (S.leqProof (knownNat @1) n)
      pf2@S.LeqProof <- return $ S.leqAdd (S.leqRefl (knownNat @1)) idx
      Refl <- return $ S.plusComm (knownNat @1) idx
      pf3@S.LeqProof <- return $ S.leqTrans pf2 pf1
      S.LeqProof <- return $ S.leqTrans pf3 (S.leqProof (idx `addNat` n) w)
      bvShf <- addExpr (AppExpr (M.BVShr w bvVal (M.mkLit w (intValue idx))))
      return $ AppExpr (M.Trunc bvShf n)
    False -> do
      -- Is there a way to just "know" that n = w?
      Just Refl <- return $ testEquality n w
      return $ ValueExpr bvVal
crucAppToExpr (S.BVTestBit idx bv) = AppExpr <$> do
  M.BVTestBit
    <$> addExpr (ValueExpr (M.BVValue (S.bvWidth bv) (fromIntegral idx)))
    <*> addElt bv

crucAppToExpr (S.SemiRingSum sm) =
    case WSum.sumRepr sm of
      SR.SemiRingBVRepr SR.BVArithRepr w ->
        let smul mul e = do x <- sval mul
                            y <- eltToExpr e
                            AppExpr <$> do M.BVMul w <$> addExpr x <*> addExpr y
            sval v = return $ ValueExpr $ M.BVValue w v
            add x y = AppExpr <$> do M.BVAdd w <$> addExpr x <*> addExpr y
        in WSum.evalM add smul sval sm
      SR.SemiRingBVRepr SR.BVBitsRepr w ->
        let smul mul e = do x <- sval mul
                            y <- eltToExpr e
                            AppExpr <$> do M.BVAnd w <$> addExpr x <*> addExpr y
            sval v = return $ ValueExpr $ M.BVValue w v
            add x y = AppExpr <$> do M.BVXor w <$> addExpr x <*> addExpr y
        in WSum.evalM add smul sval sm
      _ -> error "unsupported SemiRingSum repr for macaw PPC base semantics"

crucAppToExpr (S.SemiRingProd pd) =
    case WSum.prodRepr pd of
      SR.SemiRingBVRepr SR.BVArithRepr w ->
        let pmul x y = AppExpr <$> do M.BVMul w <$> addExpr x <*> addExpr y
            unit = return $ ValueExpr $ M.BVValue w 1
        in WSum.prodEvalM pmul eltToExpr pd >>= maybe unit return
      SR.SemiRingBVRepr SR.BVBitsRepr w ->
        let pmul x y = AppExpr <$> do M.BVAnd w <$> addExpr x <*> addExpr y
            unit = return $ ValueExpr $ M.BVValue w $ S.maxUnsigned w
        in WSum.prodEvalM pmul eltToExpr pd >>= maybe unit return
      _ -> error "unsupported SemiRingProd repr for macaw PPC base semantics"

crucAppToExpr (S.BVOrBits pd) =
    case WSum.prodRepr pd of
      SR.SemiRingBVRepr _ w ->
        let pmul x y = AppExpr <$> do M.BVOr w <$> addExpr x <*> addExpr y
            unit = return $ ValueExpr $ M.BVValue w 0
        in WSum.prodEvalM pmul eltToExpr pd >>= maybe unit return

crucAppToExpr (S.BVShl repr bv1 bv2) = AppExpr <$> do
  M.BVShl <$> pure repr <*> addElt bv1 <*> addElt bv2
crucAppToExpr (S.BVLshr repr bv1 bv2) = AppExpr <$> do
  M.BVShr <$> pure repr <*> addElt bv1 <*> addElt bv2
crucAppToExpr (S.BVAshr repr bv1 bv2) = AppExpr <$> do
  M.BVSar <$> pure repr <*> addElt bv1 <*> addElt bv2
crucAppToExpr (S.BVZext repr bv) = AppExpr <$> do
  M.UExt <$> addElt bv <*> pure repr
crucAppToExpr (S.BVSext repr bv) = AppExpr <$> do
  M.SExt <$> addElt bv <*> pure repr

crucAppToExpr _ = error "crucAppToExpr: unimplemented crucible operation"


data BoolMapOp = AndOp | OrOp

evalBoolMap :: M.ArchConstraints ppc =>
               BoolMapOp -> Bool -> BooM.BoolMap (S.Expr t)
            -> Generator ppc ids s (Expr ppc ids 'M.BoolType)
evalBoolMap op defVal bmap =
  let bBase b = return $ ValueExpr (M.BoolValue b)
      bNotBase = bBase . not
  in case BooM.viewBoolMap bmap of
       BooM.BoolMapUnit -> bBase defVal
       BooM.BoolMapDualUnit -> bNotBase defVal
       BooM.BoolMapTerms ts ->
         let onEach e r = do
               e >>= \e' -> do
                 n <- case r of
                        (t, BooM.Positive) -> eltToExpr t
                        (t, BooM.Negative) -> do p <- eltToExpr t
                                                 AppExpr <$> do M.NotApp <$> addExpr p
                 case op of
                   AndOp -> AppExpr <$> do M.AndApp <$> addExpr e' <*> addExpr n
                   OrOp  -> AppExpr <$> do M.OrApp  <$> addExpr e' <*> addExpr n
         in F.foldl onEach (bBase defVal) ts


locToReg :: (1 <= APPC.ArchRegWidth ppc,
             M.RegAddrWidth (PPCReg ppc) ~ APPC.ArchRegWidth ppc)
         => proxy ppc
         -> APPC.Location ppc ctp
         -> PPCReg ppc (FromCrucibleBaseType ctp)
locToReg _ (APPC.LocGPR gpr) = PPC_GP gpr
locToReg _  APPC.LocIP       = PPC_IP
locToReg _  APPC.LocLNK      = PPC_LNK
locToReg _  APPC.LocCTR      = PPC_CTR
locToReg _  APPC.LocCR       = PPC_CR
locToReg _  loc              = error ("macaw-ppc: Undefined location " ++ show loc)
-- fill the rest out later

-- | Given a location to modify and a crucible formula, construct a Generator that
-- will modify the location by the function encoded in the formula.
interpretFormula :: forall var ppc t ctp s ids
                  . ( ppc ~ SP.AnyPPC var
                    , PPCArchConstraints var
                    , 1 <= APPC.ArchRegWidth ppc
                    , M.RegAddrWidth (PPCReg ppc) ~ APPC.ArchRegWidth ppc
                    )
                 => APPC.Location ppc ctp
                 -> S.Expr t ctp
                 -> Generator ppc ids s ()
interpretFormula loc elt = do
  expr <- eltToExpr elt
  let reg  = (locToReg (Proxy @ppc) loc)
  case expr of
    ValueExpr val -> setRegVal reg val
    AppExpr app -> do
      assignment <- addAssignment (M.EvalApp app)
      setRegVal reg (M.AssignedValue assignment)

-- Convert a Crucible element into an expression.
eltToExpr :: M.ArchConstraints ppc =>
             S.Expr t ctp
          -> Generator ppc ids s (Expr ppc ids (FromCrucibleBaseType ctp))
eltToExpr (S.AppExpr appElt) = crucAppToExpr (S.appExprApp appElt)
eltToExpr (S.SemiRingLiteral (SR.SemiRingBVRepr _ w) val _) =
  return $ ValueExpr (M.BVValue w val)
eltToExpr _ = undefined

-- Add a Crucible element in the Generator monad.
addElt :: M.ArchConstraints ppc =>
          S.Expr t ctp
       -> Generator ppc ids s (M.Value ppc ids (FromCrucibleBaseType ctp))
addElt elt = eltToExpr elt >>= addExpr
