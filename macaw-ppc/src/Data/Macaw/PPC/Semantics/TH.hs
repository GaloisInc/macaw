{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.PPC.Semantics.TH
  ( genExecInstruction
  ) where

import qualified Data.ByteString as BS
import qualified Data.Constraint as C

import Control.Lens
import Data.Proxy
import Language.Haskell.TH
import GHC.TypeLits

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as Map
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.Witness ( Witness(..) )
import qualified Lang.Crucible.Solver.SimpleBuilder as S
import qualified Lang.Crucible.Solver.SimpleBackend as S
import qualified Lang.Crucible.BaseTypes as S

import qualified Dismantle.PPC as D
import           SemMC.Formula
import qualified SemMC.Architecture as A
import qualified SemMC.Architecture.PPC.Location as APPC
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Types as M

import Data.Parameterized.NatRepr ( knownNat
                                  , addNat
                                  , natValue
                                  , isPosNat
                                  , testLeq
                                  )

import Data.Macaw.PPC.Generator
import Data.Macaw.PPC.PPCReg

-- generate a different case for each key/value pair in the map
genExecInstruction :: (A.Architecture arch, OrdF a, ShowF a)
                   => proxy arch
                   -> (forall sh . c sh C.:- BuildOperandList arch sh)
                   -> [(Some (Witness c a), BS.ByteString)]
                   -> Q Exp
genExecInstruction _ impl semantics = do
  Some ng <- runIO PN.newIONonceGenerator
  sym <- runIO (S.newSimpleBackend ng)
  formulas <- runIO (loadFormulas sym impl semantics)
  [| undefined |]

-- SemMC.Formula: instantiateFormula

type Sym t = S.SimpleBackend t

type family FromCrucibleBaseType (btp :: S.BaseType) :: M.Type where
  FromCrucibleBaseType (S.BaseBVType w) = M.BVType w
  FromCrucibleBaseType (S.BaseBoolType) = M.BoolType

-- Unimplemented:

-- Don't need to implement:
--   - all SemiRing operations (not using)
--   - all "Basic arithmetic operations" (not using)
--   - all "Operations that introduce irrational numbers" (not using)
--   - BVUnaryTerm (not using)
--   - all array operations (probably not using)
--   - all conversions
--   - all complex operations
--   - all structs

-- Can implement now:
--   - BVTestBit

-- Might need to implement later:
--   - BVUdiv, BVUrem, BVSdiv, BVSrem

addExpr :: Expr ppc ids tp -> PPCGenerator ppc ids (M.Value ppc ids tp)
addExpr expr = do
  case expr of
    ValueExpr val -> return val
    AppExpr app -> do
      assignment <- addAssignment (M.EvalApp app)
      return $ M.AssignedValue assignment

addElt :: S.Elt t ctp -> PPCGenerator ppc ids (M.Value ppc ids (FromCrucibleBaseType ctp))
addElt elt = eltToExpr elt >>= addExpr

-- combine this with addElt
eltToExpr :: S.Elt t ctp -> PPCGenerator ppc ids (Expr ppc ids (FromCrucibleBaseType ctp))
eltToExpr (S.BVElt w val loc) = return $ ValueExpr (M.BVValue w val)
eltToExpr (S.AppElt appElt) = crucAppToExpr (S.appEltApp appElt)

crucAppToExpr :: S.App (S.Elt t) ctp -> PPCGenerator ppc ids (Expr ppc ids (FromCrucibleBaseType ctp))
crucAppToExpr S.TrueBool  = return $ ValueExpr (M.BoolValue True)
crucAppToExpr S.FalseBool = return $ ValueExpr (M.BoolValue False)
crucAppToExpr (S.NotBool bool) = AppExpr <$> do
  M.NotApp <$> addElt bool
crucAppToExpr (S.AndBool bool1 bool2) = AppExpr <$> do
  M.AndApp <$> addElt bool1 <*> addElt bool2
crucAppToExpr (S.XorBool bool1 bool2) = AppExpr <$> do
  M.XorApp <$> addElt bool1 <*> addElt bool2
crucAppToExpr (S.IteBool test t f) = AppExpr <$> do
  M.Mux <$> pure M.BoolTypeRepr <*> addElt test <*> addElt t <*> addElt f
crucAppToExpr (S.BVIte w numBranches test t f) = AppExpr <$> do -- what is numBranches for?
  M.Mux <$> pure (M.BVTypeRepr w) <*> addElt test <*> addElt t <*> addElt f
crucAppToExpr (S.BVEq bv1 bv2) = AppExpr <$> do
  M.Eq <$> addElt bv1 <*> addElt bv2
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
  S.LeqProof <- return $ S.leqAdd2 (S.leqRefl v) (S.leqProof (knownNat @1) u)
  Refl <- return $ S.plusComm u v
  bv1Ext <- addExpr (AppExpr (M.UExt bv1Val w)) ---(u `addNat` v)))
  bv2Ext <- addExpr (AppExpr (M.UExt bv2Val w))
  bv1Shifter <- addExpr (ValueExpr (M.BVValue w (natValue v)))
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
      bvShf <- addExpr (AppExpr (M.BVShr w bvVal (M.mkLit w (natValue idx))))
      return $ AppExpr (M.Trunc bvShf n)
    False -> do
      -- Is there a way to just "know" that n = w?
      Just Refl <- return $ testEquality n w
      return $ ValueExpr bvVal
crucAppToExpr (S.BVNeg w bv) = do
  bvVal  <- addElt bv
  bvComp <- addExpr (AppExpr (M.BVComplement w bvVal))
  return $ AppExpr (M.BVAdd w bvComp (M.mkLit w 1))
crucAppToExpr (S.BVTestBit idx bv) = AppExpr <$> do
  M.BVTestBit
    <$> addExpr (ValueExpr (M.BVValue (S.bvWidth bv) (fromIntegral idx)))
    <*> addElt bv
crucAppToExpr (S.BVAdd repr bv1 bv2) = AppExpr <$> do
  M.BVAdd <$> pure repr <*> addElt bv1 <*> addElt bv2
crucAppToExpr (S.BVMul repr bv1 bv2) = AppExpr <$> do
  M.BVMul <$> pure repr <*> addElt bv1 <*> addElt bv2
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
crucAppToExpr (S.BVTrunc repr bv) = AppExpr <$> do
  M.Trunc <$> addElt bv <*> pure repr
crucAppToExpr (S.BVBitNot repr bv) = AppExpr <$> do
  M.BVComplement <$> pure repr <*> addElt bv
crucAppToExpr (S.BVBitAnd repr bv1 bv2) = AppExpr <$> do
  M.BVAnd <$> pure repr <*> addElt bv1 <*> addElt bv2
crucAppToExpr (S.BVBitOr repr bv1 bv2) = AppExpr <$> do
  M.BVOr <$> pure repr <*> addElt bv1 <*> addElt bv2
crucAppToExpr (S.BVBitXor repr bv1 bv2) = AppExpr <$> do
  M.BVXor <$> pure repr <*> addElt bv1 <*> addElt bv2
crucAppToExpr _ = error "crucAppToExpr: unimplemented crucible operation"

locToReg :: (1 <= APPC.ArchRegWidth ppc,
             M.RegAddrWidth (PPCReg ppc) ~ APPC.ArchRegWidth ppc)
         => proxy ppc
         -> APPC.Location ppc ctp
         -> PPCReg ppc (FromCrucibleBaseType ctp)
locToReg _ (APPC.LocGPR gpr) = PPC_GP gpr
-- fill the rest out later

-- | Given a location to modify and a crucible formula, construct a PPCGenerator that
-- will modify the location by the function encoded in the formula.
interpretFormula :: forall tp ppc t ctp s .
                    (1 <= APPC.ArchRegWidth ppc,
                     M.RegAddrWidth (PPCReg ppc) ~ APPC.ArchRegWidth ppc)
                 => APPC.Location ppc ctp
                 -> S.Elt t ctp
                 -> PPCGenerator ppc s ()
interpretFormula loc elt = do
  expr <- eltToExpr elt
  let reg  = (locToReg (Proxy @ppc) loc)
  case expr of
    ValueExpr val -> curPPCState . M.boundValue reg .= val
    AppExpr app -> do
      assignment <- addAssignment (M.EvalApp app)
      curPPCState . M.boundValue reg .= M.AssignedValue assignment
