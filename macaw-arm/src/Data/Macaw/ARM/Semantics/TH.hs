{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.ARM.Semantics.TH
    ( armAppEvaluator
    , armNonceAppEval
    )
    where

import qualified Data.Functor.Const as C
import           Data.Macaw.ARM.ARMReg
import           Data.Macaw.ARM.Arch
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Operands as O
import           Data.Macaw.SemMC.TH ( addEltTH, natReprTH, symFnName, asName )
import           Data.Macaw.SemMC.TH.Monad
import qualified Data.Macaw.Types as M
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as Map
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy ( Proxy(..) )
import           GHC.TypeLits
import           Language.Haskell.TH
import qualified SemMC.Architecture as A
import qualified SemMC.Architecture.ARM.Eval as AE
import qualified SemMC.Architecture.ARM.Location as Loc
import qualified SemMC.Architecture.Location as L
import qualified What4.Expr.Builder as S


-- n.b. although MacawQ is a monad and therefore has a fail
-- definition, using error provides *much* better error diagnostics
-- than fail does.


-- | Called to evaluate architecture-specific applications in the
-- current Nonce context.  If this is not recognized as an
-- architecture-specific Application, return Nothing, in which case
-- the caller will try the set of default Application evaluators.
armNonceAppEval :: forall arch t fs tp
                 . (A.Architecture arch,
                    L.Location arch ~ Loc.Location arch,
                    1 <= Loc.ArchRegWidth arch,
                    M.RegAddrWidth ARMReg ~ Loc.ArchRegWidth arch)
                => BoundVarInterpretations arch t fs
                -> S.NonceApp t (S.Expr t) tp
                -> Maybe (MacawQ arch t fs Exp)
armNonceAppEval bvi nonceApp =
    -- The default nonce app eval (defaultNonceAppEvaluator in
    -- macaw-semmc:Data.Macaw.SemMC.TH) will search the
    -- A.locationFuncInterpretation alist already, and there's nothing
    -- beyond that needed here, so just handle special cases here
    case nonceApp of
      S.FnApp symFn args ->
          let nm = symFnName symFn
          in case nm of
               "uf_arm_is_r15" -> return $
                   -- This requires special handling because this can
                   -- be checking actual GPR locations or the results
                   -- of an expression extracting a register number
                   -- from an operand (i.e. a NonceAppExpr), and the
                   -- appropriate interpIsR15 instance should be
                   -- applied to the result
                   case FC.toListFC Some args of
                     [Some operand] -> do
                       -- The operand can be either a variable (TH name bound from
                       -- matching on the instruction operand list) or a call on such.
                       case operand of
                         S.BoundVarExpr bv ->
                             case (Map.lookup bv (locVars bvi), Map.lookup bv (opVars bvi)) of
                               (Just _, Just _) -> fail ("arm_is_r15 bound var is location and operand: " ++ show bv)
                               (Just loc, Nothing) -> withLocToReg $ \locToReg ->
                                 liftQ [| O.extractValue (AE.interpIsR15 (armRegToGPR $(locToReg loc))) |]
                               (Nothing, Just (C.Const name)) -> liftQ [| O.extractValue (AE.interpIsR15 $(varE name)) |]
                               (Nothing, Nothing) -> fail ("arm_is_r15 bound var not found: " ++ show bv)
                         S.NonceAppExpr nonceApp' ->
                             case S.nonceExprApp nonceApp' of
                               S.FnApp symFn' args' ->
                                   let recName = symFnName symFn' in
                                   case lookup recName (A.locationFuncInterpretation (Proxy @arch)) of
                                     Nothing -> fail ("Unsupported arm_is_r15 UF: " ++ recName)
                                     Just fi ->
                                         case FC.toListFC (asName nm bvi) args' of
                                           [] -> fail ("zero-argument arm_is_r15 uninterpreted functions\
                                                       \ are not supported: " ++ nm)
                                           argNames ->
                                               let call = appE (varE (A.exprInterpName fi)) $ foldr1 appE (map varE argNames)
                                               in liftQ [| O.extractValue (AE.interpIsR15 ($(call))) |]
                               _ -> fail ("Unsupported arm.is_r15 nonce app type")
                         _ -> fail "Unsupported operand to arm.is_r15"
                     _ -> fail ("Invalid argument list for arm.is_r15: " ++ showF args)
               _ -> Nothing -- fallback to default handling
      _ -> Nothing -- fallback to default handling




-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------

addArchAssignment :: (M.HasRepr (M.ArchFn arch (M.Value arch ids)) M.TypeRepr)
                  => M.ArchFn arch (M.Value arch ids) tp
                  -> G.Generator arch ids s (G.Expr arch ids tp)
addArchAssignment expr = (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn expr (M.typeRepr expr))


armAppEvaluator :: (L.Location arch ~ Loc.Location arch,
                    A.Architecture arch,
                    1 <= Loc.ArchRegWidth arch,
                    M.RegAddrWidth ARMReg ~ Loc.ArchRegWidth arch)
                => BoundVarInterpretations arch t fs
                -> S.App (S.Expr t) ctp
                -> Maybe (MacawQ arch t fs Exp)
armAppEvaluator interps elt =
    case elt of
      S.BVUrem w bv1 bv2 -> return $ do
                              e1 <- addEltTH interps bv1
                              e2 <- addEltTH interps bv2
                              liftQ [| addArchAssignment (URem $(natReprTH w) $(return e1) $(return e2))
                                     |]
      -- S.NoPrimKnown w rhs -> return $ do e1 <- addEltTH interps rhs
      --                                   liftQ [| let npkExp = NoPrimKnown $(natReprTH w) $(return e1)
      --                                            in (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn noPrimKnown (M.typeRepr noPrimKnown))
      --                                         |]
      _ -> Nothing
