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

import qualified Control.Monad.Except as E
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
import qualified SemMC.Architecture.AArch32 as ARM
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
armNonceAppEval :: forall t fs tp .
                   BoundVarInterpretations ARM.AArch32 t fs
                -> WB.NonceApp t (WB.Expr t) tp
                -> Maybe (MacawQ ARM.AArch32 t fs Exp)
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
          "uf_simd_set" ->
            case args of
              Ctx.Empty Ctx.:> rgf Ctx.:> rid Ctx.:> val -> Just $ do
                rgf <- addEltTH M.LittleEndian bvi rgf
                rid <- addEltTH M.LittleEndian bvi rid
                val <- addEltTH M.LittleEndian bvi val
                liftQ [| do reg <- case $(return rid) of
                              M.BVValue w i | intValue w == 5, Just reg <- integerToReg i -> return reg
                              _ -> E.throwError (G.GeneratorMessage $ "SIMD identifier not concrete (uf_simd_set): " <> show (M.ppValueAssignments $(return rid)))
                            G.setRegVal reg $(return val)
                            return $(return rgf)
                       |]
              _ -> fail "Invalid uf_simd_get"
          "uf_gpr_set" ->
            case args of
              Ctx.Empty Ctx.:> rgf Ctx.:> rid Ctx.:> val -> Just $ do
                rgf <- addEltTH M.LittleEndian bvi rgf
                rid <- addEltTH M.LittleEndian bvi rid
                val <- addEltTH M.LittleEndian bvi val
                liftQ [| do reg <- case $(return rid) of
                              M.BVValue w i | intValue w == 4, Just reg <- integerToReg i -> return reg
                              _ -> E.throwError (G.GeneratorMessage $ "GPR identifier not concrete (uf_gpr_set): " <> show (M.ppValueAssignments $(return rid)))
                            G.setRegVal reg $(return val)
                            return $(return rgf)
                       |]
              _ -> fail "Invalid uf_gpr_get"
          "uf_simd_get" ->
            case args of
              Ctx.Empty Ctx.:> _array Ctx.:> ix ->
                Just $ do
                  rid <- addEltTH M.LittleEndian bvi ix
                  liftQ [| do reg <- case $(return rid) of
                                M.BVValue w i | intValue w == 5, Just reg <- integerToSIMDReg i -> return reg
                                _ -> E.throwError (G.GeneratorMessage $ "SIMD identifier not concrete (uf_simd_get: " <> show (M.ppValueAssignments $(return rid)))
                              G.getRegVal reg
                         |]
              _ -> fail "Invalid uf_simd_get"
          "uf_gpr_get" ->
            case args of
              Ctx.Empty Ctx.:> _array Ctx.:> ix ->
                Just $ do
                  rid <- addEltTH M.LittleEndian bvi ix
                  liftQ [| do reg <- case $(return rid) of
                                M.BVValue w i | intValue w == 4, Just reg <- integerToReg i -> return reg
                                _ -> E.throwError (G.GeneratorMessage $ "GPR identifier not concrete (uf_gpr_get): " <> show (M.ppValueAssignments $(return rid)))
                              G.getRegVal reg
                         |]
              _ -> fail "Invalid uf_gpr_get"
          "uf_init_gprs" -> Just $ liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined (M.TupleTypeRepr L.Nil)) |]
          "uf_init_simds" -> Just $ liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined (M.TupleTypeRepr L.Nil)) |]
          _ | "uf_assertBV_" `isPrefixOf` fnName ->
            case args of
              Ctx.Empty Ctx.:> assert Ctx.:> bv -> Just $ do
                assertTH <- addEltTH M.LittleEndian bvi assert
                bv <- addEltTH M.LittleEndian bvi bv
                liftQ [| case $(return assertTH) of
                          M.BoolValue True -> return $(return bv)
                          M.BoolValue False -> E.throwError (G.GeneratorMessage $ "Bitvector length assertion failed!")
                          -- FIXME: THIS SHOULD THROW AN ERROR
                          _ -> return $(return bv)
                          -- nm -> E.throwError (G.GeneratorMessage $ "Bitvector length assertion failed: <FIXME: PRINT NAME>")
                       |]
              _ -> fail "Invalid call to assertBV"

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

addArchAssignment :: (M.HasRepr (M.ArchFn ARM.AArch32 (M.Value ARM.AArch32 ids)) M.TypeRepr)
                  => M.ArchFn ARM.AArch32 (M.Value ARM.AArch32 ids) tp
                  -> G.Generator ARM.AArch32 ids s (G.Expr ARM.AArch32 ids tp)
addArchAssignment expr = (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn expr (M.typeRepr expr))


armAppEvaluator :: M.Endianness
                -> BoundVarInterpretations ARM.AArch32 t fs
                -> WB.App (WB.Expr t) ctp
                -> Maybe (MacawQ ARM.AArch32 t fs Exp)
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
