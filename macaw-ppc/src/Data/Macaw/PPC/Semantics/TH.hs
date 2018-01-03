{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
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
import           GHC.TypeLits

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as Map
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Lang.Crucible.Solver.SimpleBuilder as S

import qualified SemMC.Architecture as A
import qualified SemMC.Architecture.Location as L
import qualified SemMC.Architecture.PPC.Eval as PE
import qualified SemMC.Architecture.PPC.Location as APPC
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as M

import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Operands as O
import           Data.Macaw.SemMC.TH.Monad
import           Data.Macaw.SemMC.TH ( natReprTH, addEltTH, symFnName, asName )

import           Data.Macaw.PPC.Arch
import           Data.Macaw.PPC.PPCReg

ppcNonceAppEval :: forall arch t tp
                 . (A.Architecture arch,
                    L.Location arch ~ APPC.Location arch,
                    1 <= APPC.ArchRegWidth arch,
                    M.RegAddrWidth (PPCReg arch) ~ APPC.ArchRegWidth arch)
                => BoundVarInterpretations arch t
                -> S.NonceApp t (S.Elt t) tp
                -> Maybe (MacawQ arch t Exp)
ppcNonceAppEval bvi nonceApp =
  case nonceApp of
    S.FnApp symFn args -> do
      let fnName = symFnName symFn
      case fnName of
        "ppc_is_r0" -> return $ do
          case FC.toListFC Some args of
            [Some operand] -> do
              -- The operand can be either a variable (TH name bound from
              -- matching on the instruction operand list) or a call on such.
              case operand of
                S.BoundVarElt bv -> do
                  case Map.lookup bv (opVars bvi) of
                    Just (C.Const name) -> liftQ [| O.extractValue (PE.interpIsR0 $(varE name)) |]
                    Nothing -> fail ("bound var not found: " ++ show bv)
                S.NonceAppElt nonceApp' -> do
                  case S.nonceEltApp nonceApp' of
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
elementaryFPName = L.stripPrefix "fp_"

addArchAssignment :: (M.HasRepr (M.ArchFn arch (M.Value arch ids)) M.TypeRepr)
                  => M.ArchFn arch (M.Value arch ids) tp
                  -> G.Generator arch ids s (G.Expr arch ids tp)
addArchAssignment expr = (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn expr (M.typeRepr expr))

addArchExpr :: (MM.MemWidth (M.RegAddrWidth (M.ArchReg arch)),
                OrdF (M.ArchReg arch),
                M.HasRepr (M.ArchFn arch (M.Value arch ids)) M.TypeRepr)
            => M.ArchFn arch (M.Value arch ids) tp
            -> G.Generator arch ids s (M.Value arch ids tp)
addArchExpr archfn = do
  asgn <- G.addAssignment (M.EvalArchFn archfn (M.typeRepr archfn))
  G.addExpr (G.ValueExpr (M.AssignedValue asgn))

floatingPointTH :: forall arch t f c
                 . (L.Location arch ~ APPC.Location arch,
                     A.Architecture arch,
                     1 <= APPC.ArchRegWidth arch,
                     M.RegAddrWidth (PPCReg arch) ~ APPC.ArchRegWidth arch,
                     FC.FoldableFC f)
                 => BoundVarInterpretations arch t
                 -> String
                 -> f (S.Elt t) c
                 -> MacawQ arch t Exp
floatingPointTH bvi fnName args =
  case FC.toListFC Some args of
    [Some a] ->
      case fnName of
        "round_single" -> do
          fpval <- addEltTH bvi a
          liftQ [| addArchExpr (FPCvt M.DoubleFloatRepr $(return fpval) M.SingleFloatRepr) |]
        "single_to_double" -> do
          fpval <- addEltTH bvi a
          liftQ [| addArchExpr (FPCvt M.SingleFloatRepr $(return fpval) M.DoubleFloatRepr) |]
        "abs" -> do
          -- Note that fabs is only defined for doubles; the operation is the
          -- same for single and double precision on PPC, so there is only a
          -- single instruction.
          fpval <- addEltTH bvi a
          liftQ [| addArchExpr (FPAbs M.DoubleFloatRepr $(return fpval)) |]
        "negate64" -> do
          fpval <- addEltTH bvi a
          liftQ [| addArchExpr (FPNeg M.DoubleFloatRepr $(return fpval)) |]
        "negate32" -> do
          fpval <- addEltTH bvi a
          liftQ [| addArchExpr (FPNeg M.SingleFloatRepr $(return fpval)) |]
        "is_qnan32" -> do
          fpval <- addEltTH bvi a
          liftQ [| addArchExpr (FPIsQNaN M.SingleFloatRepr $(return fpval)) |]
        "is_qnan64" -> do
          fpval <- addEltTH bvi a
          liftQ [| addArchExpr (FPIsQNaN M.DoubleFloatRepr $(return fpval)) |]
        "is_snan32" -> do
          fpval <- addEltTH bvi a
          liftQ [| addArchExpr (FPIsSNaN M.SingleFloatRepr $(return fpval)) |]
        "is_snan64" -> do
          fpval <- addEltTH bvi a
          liftQ [| addArchExpr (FPIsSNaN M.DoubleFloatRepr $(return fpval)) |]
        _ -> fail ("Unsupported unary floating point intrinsic: " ++ fnName)
    [Some a, Some b] ->
      case fnName of
        "add64" -> do
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          liftQ [| addArchExpr (FPAdd M.DoubleFloatRepr $(return valA) $(return valB)) |]
        "add32" -> do
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          liftQ [| addArchExpr (FPAdd M.SingleFloatRepr $(return valA) $(return valB)) |]
        "sub64" -> do
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          liftQ [| addArchExpr (FPSub M.DoubleFloatRepr $(return valA) $(return valB)) |]
        "sub32" -> do
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          liftQ [| addArchExpr (FPSub M.SingleFloatRepr $(return valA) $(return valB)) |]
        "mul64" -> do
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          liftQ [| addArchExpr (FPMul M.DoubleFloatRepr $(return valA) $(return valB)) |]
        "mul32" -> do
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          liftQ [| addArchExpr (FPMul M.SingleFloatRepr $(return valA) $(return valB)) |]
        "div64" -> do
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          liftQ [| addArchExpr (FPDiv M.DoubleFloatRepr $(return valA) $(return valB)) |]
        "div32" -> do
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          liftQ [| addArchExpr (FPDiv M.SingleFloatRepr $(return valA) $(return valB)) |]
        "lt" -> do
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          -- All comparisons are done as 64-bit comparisons in PPC
          liftQ [| addArchExpr (FPLt M.DoubleFloatRepr $(return valA) $(return valB)) |]
        _ -> fail ("Unsupported binary floating point intrinsic: " ++ fnName)
    [Some a, Some b, Some c] ->
      case fnName of
        "muladd64" -> do
          -- FIXME: This is very wrong - we need a separate constructor for it
          -- a * c + b
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          valC <- addEltTH bvi c
          liftQ [| do prodVal <- addArchExpr (FPMul M.DoubleFloatRepr $(return valA) $(return valC))
                      addArchExpr (FPAdd M.DoubleFloatRepr prodVal $(return valB))
                 |]
        "muladd32" -> do
          -- a * c + b
          valA <- addEltTH bvi a
          valB <- addEltTH bvi b
          valC <- addEltTH bvi c
          liftQ [| do prodVal <- addArchExpr (FPMul M.SingleFloatRepr $(return valA) $(return valC))
                      addArchExpr (FPAdd M.SingleFloatRepr prodVal $(return valB))
                 |]
        _ -> fail ("Unsupported ternary floating point intrinsic: " ++ fnName)
    _ -> fail ("Unsupported floating point intrinsic: " ++ fnName)

ppcAppEvaluator :: (L.Location arch ~ APPC.Location arch,
                    A.Architecture arch,
                    1 <= APPC.ArchRegWidth arch,
                    M.RegAddrWidth (PPCReg arch) ~ APPC.ArchRegWidth arch)
                => BoundVarInterpretations arch t
                -> S.App (S.Elt t) ctp
                -> Maybe (MacawQ arch t Exp)
ppcAppEvaluator interps elt = case elt of
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
  _ -> Nothing
