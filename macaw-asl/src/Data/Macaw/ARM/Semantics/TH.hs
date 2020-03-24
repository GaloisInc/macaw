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

import qualified Control.Monad.Error as E
import qualified Data.Functor.Const as C
import           Data.List (isPrefixOf)
import           Data.Macaw.ARM.ARMReg
import           Data.Macaw.ARM.Arch
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Operands as O
import           Data.Macaw.SemMC.TH ( addEltTH, natReprTH, symFnName, asName )
import           Data.Macaw.SemMC.TH.Monad
import qualified Data.Macaw.Types as M
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import qualified Data.Parameterized.List as L
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
import qualified What4.BaseTypes as WT
import qualified What4.Expr.Builder as WB


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
                -> WB.NonceApp t (WB.Expr t) tp
                -> Maybe (MacawQ arch t fs Exp)
armNonceAppEval bvi nonceApp =
    -- The default nonce app eval (defaultNonceAppEvaluator in
    -- macaw-semmc:Data.Macaw.SemMC.TH) will search the
    -- A.locationFuncInterpretation alist already, and there's nothing
    -- beyond that needed here, so just handle special cases here
    case nonceApp of
      WB.FnApp symFn args ->
        let fnName = symFnName symFn
            tp = WB.symFnReturnType symFn
        in case fnName of
          "uf_gpr_set" -> Just $ liftQ [| error $ "gpr_set " <> $(return $ LitE (StringL (showF tp))) |]
          "uf_write_mem_32" -> Just $ liftQ [| error $ "write_mem " <> $(return $ LitE (StringL (showF tp))) |]
          "uf_simd_get" ->
             case args of
               Ctx.Empty Ctx.:> _array Ctx.:> ix ->
                 Just $ do
                   rid <- addEltTH M.LittleEndian bvi ix
                   liftQ [| E.throwError (G.GeneratorMessage "SIMD values not handled yet") |]
          "uf_gpr_get" ->
             case args of
               Ctx.Empty Ctx.:> _array Ctx.:> ix ->
                 Just $ do
                   rid <- addEltTH M.LittleEndian bvi ix
                   liftQ [| do reg <- case $(return rid) of
                                        M.BVValue w i | intValue w == 4, Just reg <- integerToARMReg i -> return reg
                                        _ -> E.throwError (G.GeneratorMessage "Register identifier not concrete")
                               G.getRegVal reg
                          |]
                   -- liftQ [| do G.getRegVal $(return rid)
                   --        |]
          "uf_init_gprs" -> Just $ liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined (M.TupleTypeRepr L.Nil)) |]
          "uf_init_simds" -> Just $ liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined (M.TupleTypeRepr L.Nil)) |]
          _ | "uf_UNDEFINED_" `isPrefixOf` fnName ->
               Just $ liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined $(what4TypeTH tp)) |]
          _ | "uf_INIT_GLOBAL_" `isPrefixOf` fnName ->
               Just $ liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined $(what4TypeTH tp)) |]
          _ -> Nothing
      _ -> Nothing -- fallback to default handling

what4TypeTH :: WT.BaseTypeRepr tp -> Q Exp
what4TypeTH (WT.BaseBVRepr natRepr) = [| M.BVTypeRepr $(natReprTH natRepr) |]
what4TypeTH WT.BaseBoolRepr = [| M.BoolTypeRepr |]
what4TypeTH tp = error $ "Unsupported base type: " <> show tp


-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------

addArchAssignment :: (M.HasRepr (M.ArchFn arch (M.Value arch ids)) M.TypeRepr)
                  => M.ArchFn arch (M.Value arch ids) tp
                  -> G.Generator arch ids s (G.Expr arch ids tp)
addArchAssignment expr = (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn expr (M.typeRepr expr))


armAppEvaluator :: (L.Location arch ~ Loc.Location arch,
                    A.Architecture arch)
                => M.Endianness
                -> BoundVarInterpretations arch t fs
                -> WB.App (WB.Expr t) ctp
                -> Maybe (MacawQ arch t fs Exp)
armAppEvaluator endianness interps elt =
    case elt of

      WB.BVSdiv w bv1 bv2 -> return $ do
        e1 <- addEltTH endianness interps bv1
        e2 <- addEltTH endianness interps bv2
        liftQ [| addArchAssignment (SDiv $(natReprTH w) $(return e1) $(return e2))
               |]
      WB.BVUrem w bv1 bv2 -> return $ do
        e1 <- addEltTH endianness interps bv1
        e2 <- addEltTH endianness interps bv2
        liftQ [| addArchAssignment (URem $(natReprTH w) $(return e1) $(return e2))
               |]
      WB.BVSrem w bv1 bv2 -> return $ do
        e1 <- addEltTH endianness interps bv1
        e2 <- addEltTH endianness interps bv2
        liftQ [| addArchAssignment (SRem $(natReprTH w) $(return e1) $(return e2))
               |]
      WB.IntegerToBV _ _ -> return $ liftQ [| error "IntegerToBV" |]
      WB.SBVToInteger _ -> return $ liftQ [| error "SBVToInteger" |]
      -- WB.NoPrimKnown w rhs -> return $ do e1 <- addEltTH interps rhs
      --                                   liftQ [| let npkExp = NoPrimKnown $(natReprTH w) $(return e1)
      --                                            in (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn noPrimKnown (M.typeRepr noPrimKnown))
      --                                         |]
      _ -> Nothing
