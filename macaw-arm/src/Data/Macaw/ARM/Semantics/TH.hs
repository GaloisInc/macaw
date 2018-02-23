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


-- | Called to evaluate architecture-specific applications in the
-- current Nonce context.  If this is not recognized as an
-- architecture-specific Application, return Nothing, in which case
-- the caller will try the set of default Application evaluators.
armNonceAppEval :: forall arch t tp
                 . (A.Architecture arch,
                    L.Location arch ~ Loc.Location arch,
                    1 <= Loc.ArchRegWidth arch,
                    M.RegAddrWidth ARMReg ~ Loc.ArchRegWidth arch)
                => BoundVarInterpretations arch t
                -> S.NonceApp t (S.Elt t) tp
                -> Maybe (MacawQ arch t Exp)
armNonceAppEval bvi nonceApp =
    -- The default nonce app eval (defaultNonceAppEvaluator in
    -- macaw-semmc:Data.Macaw.SemMC.TH) will search the
    -- A.locationFuncInterpretation alist already, and there's nothing
    -- beyond that needed here, so just allow the default to handle
    -- everything.
    Nothing


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
