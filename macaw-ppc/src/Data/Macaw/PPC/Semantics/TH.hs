{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.PPC.Semantics.TH (
  ppcAppEvaluator,
  ppcNonceAppEval
  ) where

import qualified Data.Functor.Const as C
import           Data.Proxy ( Proxy(..) )
import qualified Data.List as L
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (lift)
import           GHC.TypeLits

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as Map
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified What4.Expr.Builder as S
import qualified What4.Interface as S

import qualified SemMC.Architecture as A
import qualified SemMC.Architecture.Location as L
import qualified SemMC.Architecture.PPC.Eval as PE
import qualified SemMC.Architecture.PPC.Location as APPC
import qualified SemMC.Util as U
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as M

import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Operands as O
import           Data.Macaw.SemMC.TH.Monad
import           Data.Macaw.SemMC.TH ( natReprTH, floatInfoFromPrecisionTH, addEltTH, symFnName, asName )

import           Data.Macaw.PPC.Arch
import           Data.Macaw.PPC.PPCReg

getOpName :: S.Expr t x -> Maybe String
getOpName e
  | S.NonceAppExpr nae <- e
  , S.FnApp fn _ <- S.nonceExprApp nae =
    Just $ show $ S.symFnName fn
  | otherwise = Nothing

ppcNonceAppEval :: forall arch t fs tp
                 . (A.Architecture arch,
                    L.Location arch ~ APPC.Location arch,
                    1 <= APPC.ArchRegWidth arch,
                    M.RegAddrWidth (PPCReg arch) ~ APPC.ArchRegWidth arch)
                => BoundVarInterpretations arch t fs
                -> S.NonceApp t (S.Expr t) tp
                -> Maybe (MacawQ arch t fs Exp)
ppcNonceAppEval bvi nonceApp =
  case nonceApp of
    S.FnApp symFn args -> do
      let fnName = symFnName symFn
      case fnName of
        "uf_fp_un_op_fpscr" -> return $
          case FC.toListFC Some args of
            [Some op, Some frA, Some fpscr] -> case getOpName op of
              Just name -> do
                valA <- addEltTH bvi frA
                valFpscr <- addEltTH bvi fpscr
                liftQ [|
                    addArchExpr $
                      FPSCR1 $(lift name) $(return valA) $(return valFpscr)
                  |]
              Nothing ->
                fail $ "Invalid argument list for un_op_fpscr: " ++ showF args
            _ -> fail $ "Invalid argument list for un_op_fpscr: " ++ showF args
        "uf_fp_bin_op_fpscr" -> return $
          case FC.toListFC Some args of
            [Some op, Some frA, Some frB, Some fpscr] -> case getOpName op of
              Just name -> do
                valA <- addEltTH bvi frA
                valB <- addEltTH bvi frB
                valFpscr <- addEltTH bvi fpscr
                liftQ [|
                    addArchExpr $ FPSCR2
                      $(lift name)
                      $(return valA)
                      $(return valB)
                      $(return valFpscr)
                  |]
              Nothing ->
                fail $ "Invalid argument list for un_op_fpscr: " ++ showF args
            _ -> fail $ "Invalid argument list for bin_op_fpscr: " ++ showF args
        "uf_fp_tern_op_fpscr" -> return $
          case FC.toListFC Some args of
            [Some op, Some frA, Some frB, Some frC, Some fpscr] ->
              case getOpName op of
                Just name -> do
                  valA <- addEltTH bvi frA
                  valB <- addEltTH bvi frB
                  valC <- addEltTH bvi frC
                  valFpscr <- addEltTH bvi fpscr
                  liftQ [|
                      addArchExpr $ FPSCR3
                        $(lift name)
                        $(return valA)
                        $(return valB)
                        $(return valC)
                        $(return valFpscr)
                    |]
                Nothing -> fail $
                  "Invalid argument list for un_op_fpscr: " ++ showF args
            _ -> fail $ "Invalid argument list for tern_op_fpscr: " ++ showF args
        "uf_ppc_fp1" -> return $ do
          case FC.toListFC Some args of
            [Some op, Some frA, Some fpscr] -> do
              case getOpName op of
                Just name -> do
                  valA <- addEltTH bvi frA
                  valFpscr <- addEltTH bvi fpscr
                  liftQ [| addArchExpr $ FP1 $(lift name) $(return valA) $(return valFpscr) |]
                Nothing -> fail $ "Invalid argument list for ppc.fp1: " ++ showF args
            _ -> fail $ "Invalid argument list for ppc.fp1: " ++ showF args
        "uf_ppc_fp2" -> return $ do
          case FC.toListFC Some args of
            [Some op, Some frA, Some frB, Some fpscr] -> do
              case getOpName op of
                Just name -> do
                  valA <- addEltTH bvi frA
                  valB <- addEltTH bvi frB
                  valFpscr <- addEltTH bvi fpscr
                  liftQ [| addArchExpr $ FP2 $(lift name) $(return valA) $(return valB) $(return valFpscr) |]
                Nothing -> fail $ "Invalid argument list for ppc.fp2: " ++ showF args
            _ -> fail $ "Invalid argument list for ppc.fp2: " ++ showF args
        "uf_ppc_fp3" -> return $ do
          case FC.toListFC Some args of
            [Some op, Some frA, Some frB, Some frC, Some fpscr] -> do
              case getOpName op of
                Just name -> do
                  valA <- addEltTH bvi frA
                  valB <- addEltTH bvi frB
                  valC <- addEltTH bvi frC
                  valFpscr <- addEltTH bvi fpscr
                  liftQ [| addArchExpr $ FP3 $(lift name) $(return valA) $(return valB) $(return valC) $(return valFpscr) |]
                Nothing -> fail $ "Invalid argument list for ppc.fp2: " ++ showF args
            _ -> fail $ "Invalid argument list for ppc.fp2: " ++ showF args
        "uf_ppc_vec1" -> return $ do
          case FC.toListFC Some args of
            [Some op, Some rA, Some vscr] -> do
              case getOpName op of
                Just name -> do
                  valA <- addEltTH bvi rA
                  valVscr <- addEltTH bvi vscr
                  liftQ [| addArchExpr $ Vec1 $(lift name) $(return valA) $(return valVscr) |]
                Nothing -> fail $ "Invalid argument list for ppc.vec1: " ++ showF args
            _ -> fail $ "Invalid argument list for ppc.vec1: " ++ showF args
        "uf_ppc_vec2" -> return $ do
          case FC.toListFC Some args of
            [Some op, Some rA, Some rB, Some vscr] -> do
              case getOpName op of
                Just name -> do
                  valA <- addEltTH bvi rA
                  valB <- addEltTH bvi rB
                  valVscr <- addEltTH bvi vscr
                  liftQ [| addArchExpr $ Vec2 $(lift name) $(return valA) $(return valB) $(return valVscr) |]
                Nothing -> fail $ "Invalid argument list for ppc.vec2: " ++ showF args
            _ -> fail $ "Invalid argument list for ppc.vec2: " ++ showF args
        "uf_ppc_vec3" -> return $ do
          case FC.toListFC Some args of
            [Some op, Some rA, Some rB, Some rC, Some vscr] -> do
              case getOpName op of
                Just name -> do
                  valA <- addEltTH bvi rA
                  valB <- addEltTH bvi rB
                  valC <- addEltTH bvi rC
                  valVscr <- addEltTH bvi vscr
                  liftQ [| addArchExpr $ Vec3 $(lift name) $(return valA) $(return valB) $(return valC) $(return valVscr) |]
                Nothing -> fail $ "Invalid argument list for ppc.vec3: " ++ showF args
            _ -> fail $ "Invalid argument list for ppc.vec3: " ++ showF args
        "uf_ppc_is_r0" -> return $ do
          case FC.toListFC Some args of
            [Some operand] -> do
              -- The operand can be either a variable (TH name bound from
              -- matching on the instruction operand list) or a call on such.
              case operand of
                S.BoundVarExpr bv -> do
                  case Map.lookup bv (opVars bvi) of
                    Just (C.Const name) -> liftQ [| O.extractValue (PE.interpIsR0 $(varE name)) |]
                    Nothing -> fail ("bound var not found: " ++ show bv)
                S.NonceAppExpr nonceApp' -> do
                  case S.nonceExprApp nonceApp' of
                    S.FnApp symFn' args' -> do
                      let recName = symFnName symFn'
                      case lookup recName (A.locationFuncInterpretation (Proxy @arch)) of
                        Nothing -> fail ("Unsupported UF: " ++ recName)
                        Just fi -> do
                          case FC.toListFC (asName fnName bvi) args' of
                            [] -> fail ("zero-argument uninterpreted functions are not supported: " ++ fnName)
                            argNames -> do
                              let call = appE (varE (A.exprInterpName fi)) $ foldr1 appE (map varE argNames)
                              liftQ [| O.extractValue (PE.interpIsR0 ($(call))) |]
                    _ -> fail ("Unsupported nonce app type")
                _ -> fail "Unsupported operand to ppc.is_r0"
            _ -> fail ("Invalid argument list for ppc.is_r0: " ++ showF args)
        _ | Just fpFunc <- elementaryFPName fnName -> return (floatingPointTH bvi fpFunc args)
          | otherwise -> Nothing
    _ -> Nothing

elementaryFPName :: String -> Maybe String
elementaryFPName = L.stripPrefix "uf_fp_"

addArchAssignment
  :: (M.HasRepr (M.ArchFn arch (M.Value arch ids)) M.TypeRepr)
  => M.ArchFn arch (M.Value arch ids) tp
  -> G.Generator arch ids s (G.Expr arch ids tp)
addArchAssignment expr = G.ValueExpr . M.AssignedValue <$>
  G.addAssignment (M.EvalArchFn expr (M.typeRepr expr))

addArchExpr
  :: ( MM.MemWidth (M.RegAddrWidth (M.ArchReg arch))
     , OrdF (M.ArchReg arch)
     , M.HasRepr (M.ArchFn arch (M.Value arch ids)) M.TypeRepr
     )
  => M.ArchFn arch (M.Value arch ids) tp
  -> G.Generator arch ids s (M.Value arch ids tp)
addArchExpr expr = G.addExpr =<< addArchAssignment expr

floatingPointTH :: forall arch t fs f c
                 . (L.Location arch ~ APPC.Location arch,
                     A.Architecture arch,
                     1 <= APPC.ArchRegWidth arch,
                     M.RegAddrWidth (PPCReg arch) ~ APPC.ArchRegWidth arch,
                     FC.FoldableFC f)
                 => BoundVarInterpretations arch t fs
                 -> String
                 -> f (S.Expr t) c
                 -> MacawQ arch t fs Exp
floatingPointTH bvi fnName args =
  case FC.toListFC Some args of
    [Some a] -> case fnName of
      "double_to_single" -> do
        fpval <- addEltTH bvi a
        liftQ [|
            addArchExpr $
              FPCoerce M.SingleFloatRepr M.DoubleFloatRepr $(return fpval)
          |]
      _ -> fail ("Unsupported unary floating point intrinsic: " ++ fnName)
    [Some _a, Some _b] ->
      case fnName of
        _ -> fail ("Unsupported binary floating point intrinsic: " ++ fnName)
    [Some _a, Some _b, Some _c] ->
      case fnName of
        _ -> fail ("Unsupported ternary floating point intrinsic: " ++ fnName)
    _ -> fail ("Unsupported floating point intrinsic: " ++ fnName)

ppcAppEvaluator :: (L.Location arch ~ APPC.Location arch,
                    A.Architecture arch,
                    1 <= APPC.ArchRegWidth arch,
                    M.RegAddrWidth (PPCReg arch) ~ APPC.ArchRegWidth arch)
                => BoundVarInterpretations arch t fs
                -> S.App (S.Expr t) ctp
                -> Maybe (MacawQ arch t fs Exp)
ppcAppEvaluator interps = \case
  S.BVSdiv w bv1 bv2 -> return $ do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| addArchAssignment (SDiv $(natReprTH w) $(return e1) $(return e2))
           |]
  S.BVUdiv w bv1 bv2 -> return $ do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| addArchAssignment (UDiv $(natReprTH w) $(return e1) $(return e2))
           |]

  S.FloatNeg fpp fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $ FPNeg $(floatInfoFromPrecisionTH fpp) $(return e)
      |]
  S.FloatAbs fpp fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $ FPAbs $(floatInfoFromPrecisionTH fpp) $(return e)
      |]
  S.FloatSqrt fpp r fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $ FPSqrt
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e)
      |]

  S.FloatAdd fpp r fp1 fp2 -> return $ do
    e1 <- addEltTH interps fp1
    e2 <- addEltTH interps fp2
    liftQ [|
        addArchAssignment $ FPAdd
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e1)
          $(return e2)
      |]
  S.FloatSub fpp r fp1 fp2 -> return $ do
    e1 <- addEltTH interps fp1
    e2 <- addEltTH interps fp2
    liftQ [|
        addArchAssignment $ FPSub
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e1)
          $(return e2)
      |]
  S.FloatMul fpp r fp1 fp2 -> return $ do
    e1 <- addEltTH interps fp1
    e2 <- addEltTH interps fp2
    liftQ [|
        addArchAssignment $ FPMul
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e1)
          $(return e2)
      |]
  S.FloatDiv fpp r fp1 fp2 -> return $ do
    e1 <- addEltTH interps fp1
    e2 <- addEltTH interps fp2
    liftQ [|
        addArchAssignment $ FPDiv
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e1)
          $(return e2)
      |]

  S.FloatFMA fpp r fp1 fp2 fp3 -> return $ do
    e1 <- addEltTH interps fp1
    e2 <- addEltTH interps fp2
    e3 <- addEltTH interps fp3
    liftQ [|
        addArchAssignment $ FPFMA
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e1)
          $(return e2)
          $(return e3)
      |]

  S.FloatLt fp1 fp2 -> return $ do
    e1 <- addEltTH interps fp1
    e2 <- addEltTH interps fp2
    liftQ [| addArchAssignment $ FPLt $(return e1) $(return e2) |]
  S.FloatFpEq fp1 fp2 -> return $ do
    e1 <- addEltTH interps fp1
    e2 <- addEltTH interps fp2
    liftQ [| addArchAssignment $ FPEq $(return e1) $(return e2) |]
  S.FloatLe fp1 fp2 -> return $ do
    e1 <- addEltTH interps fp1
    e2 <- addEltTH interps fp2
    liftQ [| addArchAssignment $ FPLe $(return e1) $(return e2) |]

  S.FloatIsNaN fp -> return $ do
    e <- addEltTH interps fp
    liftQ [| addArchAssignment $ FPIsNaN $(return e) |]

  S.FloatCast fpp r fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $ FPCast
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e)
      |]
  S.FloatRound fpp r fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $ FPRound
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e)
      |]
  S.FloatToBinary fpp fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $
          FPToBinary $(floatInfoFromPrecisionTH fpp) $(return e)
      |]
  S.FloatFromBinary fpp fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $
          FPFromBinary $(floatInfoFromPrecisionTH fpp) $(return e)
      |]
  S.FloatToSBV w r fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $
          FPToSBV $(natReprTH w) $(roundingModeToBitsTH r) $(return e)
      |]
  S.FloatToBV w r fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $
          FPToUBV $(natReprTH w) $(roundingModeToBitsTH r) $(return e)
      |]
  S.SBVToFloat fpp r fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $ FPFromUBV
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e)
      |]
  S.BVToFloat fpp r fp -> return $ do
    e <- addEltTH interps fp
    liftQ [|
        addArchAssignment $ FPFromUBV
          $(floatInfoFromPrecisionTH fpp)
          $(roundingModeToBitsTH r)
          $(return e)
      |]

  _ -> Nothing

roundingModeToBitsTH :: S.RoundingMode -> Q Exp
roundingModeToBitsTH r =
  [| M.BVValue $(natReprTH (M.knownNat @2)) $(lift $ U.roundingModeToBits r) |]
