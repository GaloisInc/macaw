{-# LANGUAGE DataKinds #-}
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
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.SemMC.Operands as O
import           Data.Macaw.SemMC.TH ( symFnName, asName )
import           Data.Macaw.SemMC.TH.Monad
import qualified Data.Macaw.Types as M
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as Map
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy ( Proxy(..) )
import           Data.Semigroup
import           GHC.TypeLits
import qualified Lang.Crucible.Solver.SimpleBuilder as S
import           Language.Haskell.TH
import qualified SemMC.Architecture as A
import qualified SemMC.Architecture.ARM.Eval as AE
import qualified SemMC.Architecture.ARM.Location as Loc
import qualified SemMC.Architecture.Location as L


-- n.b. although MacawQ is a monad and therefore has a fail
-- definition, using error provides *much* better error diagnostics
-- than fail does.


armNonceAppEval :: forall arch t tp
                 . (A.Architecture arch,
                    L.Location arch ~ Loc.Location arch,
                    1 <= Loc.ArchRegWidth arch,
                    M.RegAddrWidth ARMReg ~ Loc.ArchRegWidth arch)
                => BoundVarInterpretations arch t
                -> S.NonceApp t (S.Elt t) tp
                -> Maybe (MacawQ arch t Exp)
armNonceAppEval bvi nonceApp =
    case nonceApp of
      S.FnApp symFn args ->
          let nm = symFnName symFn
          in case nm of
               "arm_is_r15" ->
                   case FC.toListFC Some args of
                     [Some operand] ->
                         -- The operand can be either a variable (TH name bound from
                         -- matching on the instruction operand list) or a call on such.
                         case operand of
                           S.BoundVarElt bv -> appToBoundVar bvi bv nm [| AE.interpIsR15 |]
                           S.NonceAppElt nonceApp' -> appToCall bvi nonceApp' nm [| AE.interpIsR15 |]
                           _ -> error ("Argument to FnApp of \"" ++ nm ++ "\" is unhandled type: " ++ showF args)
                     a -> error $ "FnApp of \"" ++ nm ++ "\" takes 1 argument, but given " ++ show (length a)
               _ -> error $ "TBD: armNonceAppEval of FnApp \"" <> nm <> "\" is not defined"
      _ -> error $ "TBD: armNonceAppEval of something else"

appToBoundVar :: forall arch t tp.
                 BoundVarInterpretations arch t
              -> S.SimpleBoundVar t tp
              -> String
              -> ExpQ
              -> Maybe (MacawQ arch t Exp)
appToBoundVar bvi bv nm fn =
    case Map.lookup bv (opVars bvi) of
      Just (C.Const name) -> return $ liftQ [| O.extractValue $(appE fn (varE name)) |]
      Nothing -> error ("bound var \"" ++ show bv ++ "\" not found for passing to \"" ++ nm ++ "\"")

appToCall :: forall arch t tp.
             (A.Architecture arch) =>
             BoundVarInterpretations arch t
          -> S.NonceAppElt t tp
          -> String
          -> ExpQ
          -> Maybe (MacawQ arch t Exp)
appToCall bvi nonceApp' nm fn =
  case S.nonceEltApp nonceApp' of
    S.FnApp symFn' args' ->
        let recName = symFnName symFn'
        in case lookup recName (A.locationFuncInterpretation (Proxy @arch)) of
             Nothing -> error $ "Unsupported UF: " ++ recName
             Just fi ->
                 case FC.toListFC (asName nm bvi) args' of
                   [] -> error $ "zero-argument uninterpreted functions are not supported: " ++ nm
                   argNames ->
                       do let call = appE (varE (A.exprInterpName fi)) $ foldr1 appE (map varE argNames)
                          return $ liftQ [| O.extractValue $(appE fn (call)) |]
    _ -> error $ "Unsupported operand to " <> nm


armAppEvaluator :: (L.Location arch ~ Loc.Location arch,
                    A.Architecture arch,
                    1 <= Loc.ArchRegWidth arch,
                    M.RegAddrWidth ARMReg ~ Loc.ArchRegWidth arch)
                => BoundVarInterpretations arch t
                -> S.App (S.Elt t) ctp
                -> Maybe (MacawQ arch t Exp)
armAppEvaluator interps elt =
    case elt of
      -- S.NoPrimKnown w rhs -> return $ do e1 <- addEltTH interps rhs
      --                                   liftQ [| let npkExp = NoPrimKnown $(natReprTH w) $(return e1)
      --                                            in (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn noPrimKnown (M.typeRepr noPrimKnown))
      --                                         |]
      _ -> Nothing
