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

import Data.Parameterized.NatRepr (knownNat)

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
--   - BVConcat (shifts, extensions and adds?)
--   - BVSelect
--   - BVNeg (complement, add 1)
--   - BVTestBit

-- Might need to implement later:
--   - BVUdiv, BVUrem, BVSdiv, BVSrem

data Hole = Hole

addExpr :: Expr ppc ids tp -> PPCGenerator ppc ids (M.Value ppc ids tp)
addExpr expr = do
  case expr of
    ValueExpr val -> return val
    AppExpr app -> do
      assignment <- addAssignment (M.EvalApp app)
      return $ M.AssignedValue assignment

addElt :: S.Elt t ctp -> PPCGenerator ppc ids (M.Value ppc ids (FromCrucibleBaseType ctp))
addElt elt = eltToExpr elt >>= addExpr

crucAppToExpr :: S.App (S.Elt t) ctp -> PPCGenerator ppc ids (Expr ppc ids (FromCrucibleBaseType ctp))
crucAppToExpr S.TrueBool  = return $ ValueExpr (M.BoolValue True)
crucAppToExpr S.FalseBool = return $ ValueExpr (M.BoolValue False)
crucAppToExpr (S.NotBool bool) = do
  subExpr <- eltToExpr bool
  val <- addExpr subExpr
  return $ AppExpr (M.NotApp val)
crucAppToExpr (S.AndBool bool1 bool2) = do
  [val1, val2] <- sequence $ fmap addElt [bool1, bool2]
  return $ AppExpr (M.AndApp val1 val2)
crucAppToExpr (S.XorBool bool1 bool2) = do
  [val1, val2] <- sequence $ fmap addElt [bool1, bool2]
  return $ AppExpr (M.XorApp val1 val2)
crucAppToExpr (S.IteBool test t f) = do
  [testVal, tVal, fVal] <- sequence $ fmap addElt [test, t, f]
  return $ AppExpr (M.Mux M.BoolTypeRepr testVal tVal fVal)
crucAppToExpr (S.BVIte w numBranches test t f) = do -- what is numBranches for?
  testVal <- addElt test
  -- TODO: Is there any way to combine above and below into a single thing? Somehow
  -- hide the type parameter?
  [tVal, fVal] <- sequence $ fmap addElt [t, f]
  return $ AppExpr (M.Mux (M.BVTypeRepr w) testVal tVal fVal)
crucAppToExpr (S.BVEq bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.Eq bv1Val bv2Val)
crucAppToExpr (S.BVSlt bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVSignedLt bv1Val bv2Val)
crucAppToExpr (S.BVUlt bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVUnsignedLt bv1Val bv2Val)
crucAppToExpr (S.BVAdd repr bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVAdd repr bv1Val bv2Val)
crucAppToExpr (S.BVMul repr bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVMul repr bv1Val bv2Val)
crucAppToExpr (S.BVShl repr bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVShl repr bv1Val bv2Val)
crucAppToExpr (S.BVLshr repr bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVShr repr bv1Val bv2Val)
crucAppToExpr (S.BVAshr repr bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVSar repr bv1Val bv2Val)
crucAppToExpr (S.BVZext repr bv) = do
  bvVal <- addElt bv
  return $ AppExpr (M.UExt bvVal repr)
crucAppToExpr (S.BVSext repr bv) = do
  bvVal <- addElt bv
  return $ AppExpr (M.SExt bvVal repr)
crucAppToExpr (S.BVTrunc repr bv) = do
  bvVal <- addElt bv
  return $ AppExpr (M.Trunc bvVal repr)
crucAppToExpr (S.BVBitNot repr bv) = do
  bvVal <- addElt bv
  return $ AppExpr (M.BVComplement repr bvVal)
crucAppToExpr (S.BVBitAnd repr bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVAnd repr bv1Val bv2Val)
crucAppToExpr (S.BVBitOr repr bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVOr repr bv1Val bv2Val)
crucAppToExpr (S.BVBitXor repr bv1 bv2) = do
  [bv1Val, bv2Val] <- sequence $ fmap addElt [bv1, bv2]
  return $ AppExpr (M.BVXor repr bv1Val bv2Val)
crucAppToExpr _ = error "crucAppToExpr: unimplemented crucible operation"

eltToExpr :: S.Elt t ctp -> PPCGenerator ppc ids (Expr ppc ids (FromCrucibleBaseType ctp))
eltToExpr (S.BVElt w val loc) = return $ ValueExpr (M.BVValue w val)
eltToExpr (S.AppElt appElt) = crucAppToExpr (S.appEltApp appElt)

locToReg :: (1 <= APPC.ArchRegWidth ppc, M.RegAddrWidth (PPCReg ppc) ~ APPC.ArchRegWidth ppc) =>
            proxy ppc -> APPC.Location ppc ctp -> PPCReg ppc (FromCrucibleBaseType ctp)
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
