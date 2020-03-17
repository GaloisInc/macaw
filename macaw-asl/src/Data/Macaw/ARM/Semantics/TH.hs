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
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy ( Proxy(..) )
import           GHC.TypeLits
import           Language.Haskell.TH
import qualified SemMC.Architecture as A
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
                    L.Location arch ~ Loc.Location arch)
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
        let fnName = symFnName symFn
            in case fnName of
                 "uf_UNDEFINED_bitvector_1" ->
                   Just $ liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined (M.BVTypeRepr $(natReprTH (knownNat @1)))) |]
                 _ -> Nothing
      _ -> Nothing -- fallback to default handling




-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------

addArchAssignment :: (M.HasRepr (M.ArchFn arch (M.Value arch ids)) M.TypeRepr)
                  => M.ArchFn arch (M.Value arch ids) tp
                  -> G.Generator arch ids s (G.Expr arch ids tp)
addArchAssignment expr = (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn expr (M.typeRepr expr))


armAppEvaluator :: (L.Location arch ~ Loc.Location arch,
                    A.Architecture arch)
                => BoundVarInterpretations arch t fs
                -> S.App (S.Expr t) ctp
                -> Maybe (MacawQ arch t fs Exp)
armAppEvaluator interps elt =
    case elt of
      -- S.BVUrem w bv1 bv2 -> return $ do
      --                         e1 <- addEltTH interps bv1
      --                         e2 <- addEltTH interps bv2
      --                         liftQ [| addArchAssignment (URem $(natReprTH w) $(return e1) $(return e2))
      --                                |]
      -- S.NoPrimKnown w rhs -> return $ do e1 <- addEltTH interps rhs
      --                                   liftQ [| let npkExp = NoPrimKnown $(natReprTH w) $(return e1)
      --                                            in (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn noPrimKnown (M.typeRepr noPrimKnown))
      --                                         |]
      _ -> Nothing
