{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
module Data.Macaw.ARM.Semantics.TH
    ( armAppEvaluator
    , armNonceAppEval
    , getGPR
    , setGPR
    , getSIMD
    , setSIMD
    , loadSemantics
    , armTranslateType
    )
    where

import           Control.Monad ( join, void )
import qualified Control.Monad.Except as E
import qualified Data.BitVector.Sized as BVS
import           Data.List (isPrefixOf)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map
import           Data.Map ( Map )
import           Data.Macaw.ARM.ARMReg
import           Data.Macaw.ARM.Arch
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.SemMC.Generator as G
import           Data.Macaw.SemMC.TH ( addEltTH, natReprTH, symFnName, translateBaseTypeRepr )
import           Data.Macaw.SemMC.TH.Monad
import qualified Data.Macaw.Types as M
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map ( MapF )
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.NatRepr
import           GHC.TypeLits as TL
import qualified Lang.Crucible.Backend.Simple as CBS
import           Language.Haskell.TH
import qualified SemMC.Architecture.AArch32 as ARM
import qualified SemMC.Architecture.ARM.Opcodes as ARM
import qualified What4.BaseTypes as WT
import qualified What4.Expr.Builder as WB

import qualified Language.ASL.Globals as ASL

loadSemantics :: CBS.SimpleBackend t fs -> IO (ARM.ASLSemantics (CBS.SimpleBackend t fs))
loadSemantics sym = ARM.loadSemantics sym (ARM.ASLSemanticsOpts { ARM.aslOptTrimRegs = True})

-- n.b. although MacawQ is a monad and therefore has a fail
-- definition, using error provides *much* better error diagnostics
-- than fail does.

-- | Called to evaluate architecture-specific applications in the
-- current Nonce context.  If this is not recognized as an
-- architecture-specific Application, return Nothing, in which case
-- the caller will try the set of default Application evaluators.
armNonceAppEval :: forall t fs tp
                  . BoundVarInterpretations ARM.AArch32 t fs
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
          -- NOTE: The state fields corresponding to the assertion
          -- failure, undefined behavior and unpredictable behavior flags
          -- are not used, and have been wrapped in the following 3 functions.
          -- To save time, for now we can simply avoid translating them.
          
          "uf_update_assert" -> case args of
            Ctx.Empty Ctx.:> _assertVar -> Just $ do
              --assertVarE <- addEltTH M.LittleEndian bvi assertVar
              --liftQ [| $(refBinding assertVarE) |]
              liftQ [| return $ M.BoolValue False |]
            _ -> fail "Invalid uf_update_assert"
          "uf_update_undefB" -> case args of
            Ctx.Empty Ctx.:> _undefVar -> Just $ do
              --undefVarE <- addEltTH M.LittleEndian bvi undefVar
              --liftQ [| $(refBinding undefVarE) |]
              liftQ [| return $ M.BoolValue False |]
            _ -> fail "Invalid uf_update_undefB"
          "uf_update_unpredB" -> case args of
            Ctx.Empty Ctx.:> _unpredVar -> Just $ do
              --unpredVarE <- addEltTH M.LittleEndian bvi unpredVar
              --liftQ [| $(refBinding unpredVarE) |]
              liftQ [| return $ M.BoolValue False |]
            _ -> fail "Invalid uf_update_unpredB"
          "uf_simd_set" ->
            case args of
              Ctx.Empty Ctx.:> rgf Ctx.:> rid Ctx.:> val -> Just $ do
                rgfE <- addEltTH M.LittleEndian bvi rgf
                ridE <- addEltTH M.LittleEndian bvi rid
                valE <- addEltTH M.LittleEndian bvi val
                liftQ $ joinOp2 [| setSIMD $(refLazy valE) |] rgfE ridE
              _ -> fail "Invalid uf_simd_get"
          "uf_gpr_set" ->
            case args of
              Ctx.Empty Ctx.:> rgf Ctx.:> rid Ctx.:> val -> Just $ do
                rgfE <- addEltTH M.LittleEndian bvi rgf
                ridE <- addEltTH M.LittleEndian bvi rid
                valE <- addEltTH M.LittleEndian bvi val

                liftQ $ joinOp2 [| setGPR $(refLazy valE) |] rgfE ridE
              _ -> fail "Invalid uf_gpr_get"
          "uf_simd_get" ->
            case args of
              Ctx.Empty Ctx.:> simds Ctx.:> ix ->
                Just $ do
                  simdsE <- addEltTH M.LittleEndian bvi simds
                  rid <- addEltTH M.LittleEndian bvi ix
                  liftQ $ joinOp2 [| readSIMD |] simdsE rid
              _ -> fail "Invalid uf_simd_get"
          "uf_gpr_get" ->
            case args of
              Ctx.Empty Ctx.:> gprs Ctx.:> ix ->
                Just $ do
                  gprsE <- addEltTH M.LittleEndian bvi gprs
                  rid <- addEltTH M.LittleEndian bvi ix
                  liftQ $ joinOp2 [| readGPR |] gprsE rid
              _ -> fail "Invalid uf_gpr_get"
          _ | "uf_write_mem_" `isPrefixOf` fnName ->
            case args of
              Ctx.Empty Ctx.:> mem Ctx.:> addr Ctx.:> val
               | WT.BaseBVRepr memWidthRepr <- WB.exprType val ->
                 Just $ do
                memE <- addEltTH M.LittleEndian bvi mem
                addrE <- addEltTH M.LittleEndian bvi addr
                valE <- addEltTH M.LittleEndian bvi val
                let memWidth = fromIntegral (intValue memWidthRepr) `div` 8
                liftQ $ joinOp2 [| writeMem $(natReprFromIntTH memWidth) $(refLazy valE) |] memE addrE
              _ -> fail "invalid write_mem"


          _ | "uf_unsignedRSqrtEstimate" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op -> Just $ do
                  ope <- addEltTH M.LittleEndian bvi op
                  liftQ [| G.addExpr =<< $(joinOp1 [| \e1E -> addArchAssignment (UnsignedRSqrtEstimate knownNat e1E) |] ope) |]
                _ -> fail "Invalid unsignedRSqrtEstimate arguments"

          -- NOTE: This must come before fpMul, since fpMul is a prefix of this
          _ | "uf_fpMulAdd" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> op3 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  op3e <- addEltTH M.LittleEndian bvi op3
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< join ((\o1 o2 o3 o4 -> addArchAssignment (FPMulAdd knownNat o1 o2 o3 o4)) <$> $(refBinding op1e) <*> $(refBinding op2e) <*> $(refBinding op3e) <*> $(refBinding fpcre))  |]

                _ -> fail "Invalid fpMulAdd arguments"


          _ | "uf_fpSub" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPSub knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpSub arguments"
          _ | "uf_fpAdd" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPAdd knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpAdd arguments"
          _ | "uf_fpMul" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPMul knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpMul arguments"
          _ | "uf_fpDiv" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPDiv knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpDiv arguments"

          _ | "uf_fpMaxNum" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPMaxNum knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpMaxNum arguments"
          _ | "uf_fpMinNum" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPMinNum knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpMinNum arguments"
          _ | "uf_fpMax" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPMax knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpMax arguments"
          _ | "uf_fpMin" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPMin knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpMin arguments"

          _ | "uf_fpRecipEstimate" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp2 [| \e1E e2E -> addArchAssignment (FPRecipEstimate knownNat e1E e2E) |] op1e fpcre) |]
                _ -> fail "Invalid fpRecipEstimate arguments"
          _ | "uf_fpRecipStep" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  liftQ [| G.addExpr =<< $(joinOp2 [| \e1E e2E -> addArchAssignment (FPRecipStep knownNat e1E e2E) |] op1e op2e) |]
                _ -> fail "Invalid fpRecipStep arguments"
          _ | "uf_fpSqrtEstimate" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp2 [| \e1E e2E -> addArchAssignment (FPSqrtEstimate knownNat e1E e2E) |] op1e fpcre) |]
                _ -> fail "Invalid fpSqrtEstimate arguments"
          _ | "uf_fprSqrtStep" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp2 [| \e1E e2E -> addArchAssignment (FPRSqrtStep knownNat e1E e2E) |] op1e fpcre) |]
                _ -> fail "Invalid fprSqrtStep arguments"
          _ | "uf_fpSqrt" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp2 [| \e1E e2E -> addArchAssignment (FPSqrt knownNat e1E e2E) |] op1e fpcre) |]
                _ -> fail "Invalid fpSqrt arguments"

          _ | "uf_fpCompareGE" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPCompareGE knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpCompareGE arguments"
          _ | "uf_fpCompareGT" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPCompareGT knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpCompareGT arguments"
          _ | "uf_fpCompareEQ" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPCompareEQ knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpCompareEQ arguments"
          _ | "uf_fpCompareNE" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPCompareNE knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpCompareNE arguments"
          _ | "uf_fpCompareUN" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> fpcr -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  fpcre <- addEltTH M.LittleEndian bvi fpcr
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPCompareUN knownNat e1E e2E e3E) |] op1e op2e fpcre) |]
                _ -> fail "Invalid fpCompareUN arguments"

          "uf_fpToFixedJS" ->
            case args of
              Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> op3 -> Just $ do
                op1e <- addEltTH M.LittleEndian bvi op1
                op2e <- addEltTH M.LittleEndian bvi op2
                op3e <- addEltTH M.LittleEndian bvi op3
                liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPToFixedJS e1E e2E e3E) |] op1e op2e op3e) |]
              _ -> fail "Invalid fpToFixedJS arguments"
          _ | "uf_fpToFixed" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> op3 Ctx.:> op4 Ctx.:> op5 -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  op3e <- addEltTH M.LittleEndian bvi op3
                  op4e <- addEltTH M.LittleEndian bvi op4
                  op5e <- addEltTH M.LittleEndian bvi op5
                  liftQ [| G.addExpr =<< join ((\o1 o2 o3 o4 o5 -> addArchAssignment (FPToFixed knownNat o1 o2 o3 o4 o5)) <$> $(refBinding op1e) <*> $(refBinding op2e) <*> $(refBinding op3e) <*> $(refBinding op4e) <*> $(refBinding op5e)) |]
                _ -> fail "Invalid fpToFixed arguments"
          _ | "uf_fixedToFP" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> op3 Ctx.:> op4 Ctx.:> op5 -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  op3e <- addEltTH M.LittleEndian bvi op3
                  op4e <- addEltTH M.LittleEndian bvi op4
                  op5e <- addEltTH M.LittleEndian bvi op5
                  liftQ [| G.addExpr =<< join ((\o1 o2 o3 o4 o5 -> addArchAssignment (FixedToFP knownNat o1 o2 o3 o4 o5)) <$> $(refBinding op1e) <*> $(refBinding op2e) <*> $(refBinding op3e) <*> $(refBinding op4e) <*> $(refBinding op5e))  |]
                _ -> fail "Invalid fixedToFP arguments"
          _ | "uf_fpConvert" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> op3 -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  op3e <- addEltTH M.LittleEndian bvi op3
                  liftQ [| G.addExpr =<< $(joinOp3 [| \e1E e2E e3E -> addArchAssignment (FPConvert knownNat e1E e2E e3E) |] op1e op2e op3e) |]
                _ -> fail "Invalid fpConvert arguments"
          _ | "uf_fpRoundInt" `isPrefixOf` fnName ->
              case args of
                Ctx.Empty Ctx.:> op1 Ctx.:> op2 Ctx.:> op3 Ctx.:> op4 -> Just $ do
                  op1e <- addEltTH M.LittleEndian bvi op1
                  op2e <- addEltTH M.LittleEndian bvi op2
                  op3e <- addEltTH M.LittleEndian bvi op3
                  op4e <- addEltTH M.LittleEndian bvi op4
                  liftQ [| G.addExpr =<< join ((\o1 o2 o3 o4 -> addArchAssignment (FPRoundInt knownNat o1 o2 o3 o4)) <$> $(refBinding op1e) <*> $(refBinding op2e) <*> $(refBinding op3e) <*> $(refBinding op4e))  |]
                _ -> fail "Invalid fpRoundInt arguments"


          "uf_init_gprs" -> Just $ liftQ [| emptyGPRWrites |]
          "uf_init_memory" -> Just $ liftQ [| emptyMemoryWrites |]
          "uf_init_simds" -> Just $ liftQ [| emptySIMDWrites |]


          -- These functions indicate that the wrapped monadic actions in the corresponding
          -- 'ARMWriteAction' should be executed, committing their stateful actions.
          "uf_update_gprs"
            | Ctx.Empty Ctx.:> gprs <- args -> Just $ do
                gprs' <- addEltTH M.LittleEndian bvi gprs
                appendStmt $ [| join (execWriteGPRs <$> $(refBinding gprs')) |]
                setEffectful
                liftQ [| return $ unitValue |]
                  
          "uf_update_simds"
            | Ctx.Empty Ctx.:> simds <- args -> Just $ do
                simds' <- addEltTH M.LittleEndian bvi simds
                appendStmt $ [| join (execWriteSIMDs <$> $(refBinding simds')) |]
                setEffectful
                liftQ [| return $ unitValue |]

          "uf_update_memory"
            | Ctx.Empty Ctx.:> mem <- args -> Just $ do
                mem' <- addEltTH M.LittleEndian bvi mem
                appendStmt $ [| join (execMemoryWrites <$> $(refBinding mem')) |]
                setEffectful
                liftQ [| return $ unitValue |]

          "uf_noop" | Ctx.Empty <- args -> Just $ liftQ [| return $ M.BoolValue True |]

          "uf_join_units"
            | Ctx.Empty Ctx.:> u1 Ctx.:> u2 <- args -> Just $ do
                _ <- addEltTH M.LittleEndian bvi u1
                _ <- addEltTH M.LittleEndian bvi u2
                liftQ [| return $ unitValue |]
          _ | "uf_assertBV_" `isPrefixOf` fnName ->
            case args of
              Ctx.Empty Ctx.:> assert Ctx.:> bv -> Just $ do
                assertTH <- addEltTH M.LittleEndian bvi assert
                bvElt <- addEltTH M.LittleEndian bvi bv
                liftQ [| case $(refBinding assertTH) of
                          M.BoolValue True -> return $(refBinding bvElt)
                          M.BoolValue False -> E.throwError (G.GeneratorMessage $ "Bitvector length assertion failed!")
                          -- FIXME: THIS SHOULD THROW AN ERROR
                          _ -> return $(refBinding bvElt)
                          -- nm -> E.throwError (G.GeneratorMessage $ "Bitvector length assertion failed: <FIXME: PRINT NAME>")
                       |]
              _ -> fail "Invalid call to assertBV"

          _ | "uf_UNDEFINED_" `isPrefixOf` fnName ->
               Just $ liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined $(translateBaseTypeRepr tp)) |]
          _ | "uf_INIT_GLOBAL_" `isPrefixOf` fnName ->
               Just $ liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined $(translateBaseTypeRepr tp)) |]
          _ -> Nothing
      _ -> Nothing -- fallback to default handling


unitValue :: M.Value ARM.AArch32 ids (M.TupleType '[])
unitValue =  M.Initial ARMDummyReg

natReprFromIntTH :: Int -> Q Exp
natReprFromIntTH i = [| knownNat :: M.NatRepr $(litT (numTyLit (fromIntegral i))) |]

-- | A representation of an
-- un-executed effectful generator action, where 'addr' is a generalized
-- address (either a memory address, or a register number) and 'val' is the value
-- to be written.
data WriteAction f w where
  -- | A single write action 
  WriteAction :: forall f w
               . (1 <= w)
              => M.NatRepr w
              -> f M.BoolType
              -- ^ a guard which indicates whether or not this action should be committed
              -> f (M.BVType (8 TL.* w))
              -> WriteAction f w

type ARMWriteAction ids s w = WriteAction (LazyValue ids s) w

newtype ARMWriteMap ids s addr w where
  ARMWriteMap :: Map (M.Value ARM.AArch32 ids (M.BVType addr)) (ARMWriteAction ids s w) -> ARMWriteMap ids s addr w


addWriteAction :: forall addr ids w s
                . 1 <= w
               => 1 <= addr
               => NatRepr w
               -> M.Value ARM.AArch32 ids (M.BVType addr)
               -> LazyValue ids s (M.BVType (8 TL.* w))
               -> ARMWriteMap ids s addr w
               -> ARMWriteMap ids s addr w
addWriteAction valRepr addr val (ARMWriteMap wmap) =
  let
    act1 = WriteAction valRepr (EagerValue $ M.BoolValue True) val
  in case Map.lookup addr wmap of
      Just act2 ->
        let
          act = mergeActions act1 act2
        in ARMWriteMap $ Map.insert addr act wmap
      Nothing -> ARMWriteMap $ Map.insert addr act1 wmap

mergeActions :: ARMWriteAction ids s w
             -> ARMWriteAction ids s w
             -> ARMWriteAction ids s w
mergeActions (WriteAction w cond1 val1) (WriteAction _ cond2 val2) =
  let
    cond = lazyOr cond1 cond2
    val = lazyIte cond1 val1 val2
  in WriteAction w cond val

type ARMGPRWrites ids s = ARMWriteMap ids s 4 4
type ARMSIMDWrites ids s = ARMWriteMap ids s 8 16
type ARMMemoryWrites ids s = MapF NatRepr (ARMWriteMap ids s 32)


emptyGPRWrites :: G.Generator ARM.AArch32 ids s (ARMGPRWrites ids s)
emptyGPRWrites = return $ ARMWriteMap Map.empty

emptySIMDWrites :: G.Generator ARM.AArch32 ids s (ARMSIMDWrites ids s)
emptySIMDWrites = return $ ARMWriteMap Map.empty

emptyMemoryWrites :: G.Generator ARM.AArch32 ids s (ARMMemoryWrites ids s)
emptyMemoryWrites = return $ MapF.empty

singletonWriteAction :: forall addr ids w s
                      . 1 <= w
                     => 1 <= addr
                     => NatRepr w
                     -> M.Value ARM.AArch32 ids (M.BVType addr)
                     -> LazyValue ids s (M.BVType (8 TL.* w))
                     -> ARMWriteMap ids s addr w
singletonWriteAction w addr val = addWriteAction w addr val (ARMWriteMap Map.empty)


-- | Make a write action conditional on a given predicate
addWriteActionCond :: LazyValue ids s M.BoolType
                   -> ARMWriteAction ids s w
                   -> ARMWriteAction ids s w
addWriteActionCond cond1 (WriteAction w cond2 val) =
  WriteAction w (lazyAnd cond1 cond2) val

-- | Merge two write maps together, under a given condition
muxWriteMaps' :: forall ids s addr w
                . LazyValue ids s M.BoolType
               -> ARMWriteMap ids s addr w
               -> ARMWriteMap ids s addr w
               -> ARMWriteMap ids s addr w
muxWriteMaps' cond (ARMWriteMap wmapT) (ARMWriteMap wmapF) =
  let
    missingT = Map.mapMissing (\_ -> addWriteActionCond cond)
    missingF = Map.mapMissing (\_ -> addWriteActionCond (lazyNot cond))
    merge_ = Map.zipWithMatched (\_ actT actF -> muxWriteActions cond actT actF)
  in ARMWriteMap $ Map.merge missingT missingF merge_ wmapT wmapF

muxWriteMaps :: forall ids s addr w
                . LazyValue ids s M.BoolType
               -> ARMWriteMap ids s addr w
               -> ARMWriteMap ids s addr w
               -> G.Generator ARM.AArch32 ids s (ARMWriteMap ids s addr w)
muxWriteMaps cond mapT mapE = return $ muxWriteMaps' cond mapT mapE

muxMemoryWrites' :: forall ids s
                 . LazyValue ids s M.BoolType
                -> ARMMemoryWrites ids s
                -> ARMMemoryWrites ids s
                -> ARMMemoryWrites ids s
muxMemoryWrites' cond mem1 mem2 =
  let
    missingT :: ARMMemoryWrites ids s -> ARMMemoryWrites ids s
    missingT = MapF.map (\(ARMWriteMap m) ->
                           ARMWriteMap $ Map.map (addWriteActionCond cond) m)

    missingF :: ARMMemoryWrites ids s -> ARMMemoryWrites ids s
    missingF = MapF.map (\(ARMWriteMap m) ->
                           ARMWriteMap $ Map.map (addWriteActionCond (lazyNot cond)) m)

    doMerge :: forall w. NatRepr w
            -> ARMWriteMap ids s 32 w
            -> ARMWriteMap ids s 32 w
            -> Maybe (ARMWriteMap ids s 32 w)
    doMerge _ act1 act2 = Just $ muxWriteMaps' cond act1 act2

  in MapF.mergeWithKey doMerge missingT missingF mem1 mem2

muxMemoryWrites :: forall ids s
                 . LazyValue ids s M.BoolType
                -> ARMMemoryWrites ids s
                -> ARMMemoryWrites ids s
                -> G.Generator ARM.AArch32 ids s (ARMMemoryWrites ids s)
muxMemoryWrites cond mem1 mem2 = return $ muxMemoryWrites' cond mem1 mem2

muxWriteActions :: LazyValue ids s M.BoolType
                -> ARMWriteAction ids s w
                -> ARMWriteAction ids s w
                -> ARMWriteAction ids s w
muxWriteActions cond_outer (WriteAction valRepr condT valT) (WriteAction _ condF valF) =
  let
    cond = lazyIte cond_outer condT condF
    val = lazyIte cond_outer valT valF
  in WriteAction valRepr cond val

execWriteGPRs :: forall ids s
               . ARMGPRWrites ids s
              -> G.Generator ARM.AArch32 ids s ()
execWriteGPRs (ARMWriteMap wmap) = void $ Map.traverseWithKey go wmap
  where
    go :: M.Value ARM.AArch32 ids (M.BVType 4) -> ARMWriteAction ids s 4 -> G.Generator ARM.AArch32 ids s ()
    go addr (WriteAction _ cond val) =
      evalLazyWhen cond val (getGPR Current addr) (execSetGPR addr)

execWriteSIMDs :: forall ids s
                . ARMSIMDWrites ids s
               -> G.Generator ARM.AArch32 ids s ()
execWriteSIMDs (ARMWriteMap wmap) = void $ Map.traverseWithKey go wmap
  where
    go :: M.Value ARM.AArch32 ids (M.BVType 8) -> ARMWriteAction ids s 16 -> G.Generator ARM.AArch32 ids s ()
    go addr (WriteAction _ cond val) =
      evalLazyWhen cond val (getSIMD Current addr) (execSetSIMD addr)

execMemoryWrites :: forall ids s
                  . ARMMemoryWrites ids s
                 -> G.Generator ARM.AArch32 ids s ()
execMemoryWrites mem = MapF.traverseWithKey_ execW mem
  where
    execW :: forall n. NatRepr n -> ARMWriteMap ids s 32 n -> G.Generator ARM.AArch32 ids s ()
    execW _ (ARMWriteMap wmap) = void $ Map.traverseWithKey go wmap

    go :: forall n
        . M.Value ARM.AArch32 ids (M.BVType 32)
       -> ARMWriteAction ids s n
       -> G.Generator ARM.AArch32 ids s ()
    go addr (WriteAction sz cond val) =
      evalLazyWhen cond val (readMem sz addr) (execWriteMem sz addr)

writeMem :: 1 <= w
         => M.NatRepr w
         -> LazyValue ids s (M.BVType (8 TL.* w))
         -> ARMMemoryWrites ids s
         -> M.Value ARM.AArch32 ids (M.BVType 32)
         -> G.Generator ARM.AArch32 ids s (ARMMemoryWrites ids s)
writeMem sz val mem addr = case MapF.lookup sz mem of
  Just wmap -> do
    let wmap' = addWriteAction sz addr val wmap
    return $ MapF.insert sz wmap' mem
  Nothing -> do
    let wmap = singletonWriteAction sz addr val
    return $ MapF.insert sz wmap mem

readMem :: 1 <= w
        => M.NatRepr w
        -> M.Value ARM.AArch32 ids (M.BVType 32)
        -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids (M.BVType (8 TL.* w)))
readMem sz addr = M.AssignedValue <$> G.addAssignment (M.ReadMem addr (M.BVMemRepr sz M.LittleEndian))

execWriteMem :: 1 <= w
             => M.NatRepr w
             -> M.Value ARM.AArch32 ids (M.BVType 32)
             -> M.Value ARM.AArch32 ids (M.BVType (8 TL.* w))
             -> G.Generator ARM.AArch32 ids s ()
execWriteMem sz addr val = G.addStmt (M.WriteMem addr (M.BVMemRepr sz M.LittleEndian) val)

execSetGPR :: M.Value ARM.AArch32 ids (M.BVType 4)
           -> M.Value ARM.AArch32 ids (M.BVType 32)
           -> G.Generator ARM.AArch32 ids s ()
execSetGPR regid v = do
  reg <- case regid of
    M.BVValue w i
      | intValue w == 4
      , Just reg <- integerToReg i -> return reg
    _ -> E.throwError (G.GeneratorMessage $ "Bad GPR identifier (uf_gpr_set): " <> show (M.ppValueAssignments v))
  G.setRegVal reg v

setGPR :: LazyValue ids s (M.BVType 32)
       -> ARMGPRWrites ids s
       -> M.Value ARM.AArch32 ids (M.BVType 4)
       -> G.Generator ARM.AArch32 ids s (ARMGPRWrites ids s)
setGPR v acts regid = return $ addWriteAction knownNat regid v acts

data AccessMode = Current | Snapshot

-- | Read the "current" value of a GPR by first checking if it is in the
-- set of GPR writes, falling back to reading its initial snapshot value
readGPR :: ARMGPRWrites ids s
        -> M.Value ARM.AArch32 ids (M.BVType 4)
        -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids (M.BVType 32))
readGPR (ARMWriteMap acts) regid = case Map.lookup regid acts of
  Just (WriteAction _ cond v) ->
    evalLazyValue $ lazyIte cond v (LazyValue $ getGPR Snapshot regid)
  _ -> getGPR Snapshot regid

getGPR :: AccessMode
       -> M.Value ARM.AArch32 ids tp
       -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids (M.BVType 32))
getGPR mode v = do
  reg <- case v of
    M.BVValue w i
      | intValue w == 4
      , Just reg <- integerToReg i -> return reg
    _ ->  E.throwError (G.GeneratorMessage $ "Bad GPR identifier (uf_gpr_get): " <> show (M.ppValueAssignments v))
  case mode of
    Current -> G.getRegVal reg
    Snapshot -> G.getRegSnapshotVal reg

execSetSIMD :: M.Value ARM.AArch32 ids (M.BVType 8)
            -> M.Value ARM.AArch32 ids (M.BVType 128)
            -> G.Generator ARM.AArch32 ids s ()
execSetSIMD regid v = do
  reg <- case regid of
    M.BVValue w i
      | intValue w == 8
      , Just reg <- integerToSIMDReg i -> return reg
    _ -> E.throwError (G.GeneratorMessage $ "Bad SIMD identifier (uf_simd_set): " <> show (M.ppValueAssignments v))
  G.setRegVal reg v

setSIMD :: LazyValue ids s (M.BVType 128)
        -> ARMSIMDWrites ids s
        -> M.Value ARM.AArch32 ids (M.BVType 8)
        -> G.Generator ARM.AArch32 ids s (ARMSIMDWrites ids s)
setSIMD v acts regid = return $ addWriteAction knownNat regid v acts

-- | Read the "current" value of a SIMD by first checking if it is in the
-- set of SIMD writes, falling back to reading its initial snapshot value
readSIMD :: ARMSIMDWrites ids s
         -> M.Value ARM.AArch32 ids (M.BVType 8)
         -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids (M.BVType 128))
readSIMD (ARMWriteMap acts) regid = case Map.lookup regid acts of
  Just (WriteAction _ cond v) ->
    evalLazyValue $ lazyIte cond v (LazyValue $ getSIMD Snapshot regid)
  _ -> getSIMD Snapshot regid

getSIMD :: AccessMode
        -> M.Value ARM.AArch32 ids tp
        -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids (M.BVType 128))
getSIMD mode v = do
  reg <- case v of
    M.BVValue w i
      | intValue w == 8
      , Just reg <- integerToSIMDReg i -> return reg
    _ ->  E.throwError (G.GeneratorMessage $ "Bad SIMD identifier (uf_simd_get): " <> show (M.ppValueAssignments v))
  case mode of
    Current -> G.getRegVal reg
    Snapshot -> G.getRegSnapshotVal reg

-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------

addArchAssignment :: (M.HasRepr (M.ArchFn ARM.AArch32 (M.Value ARM.AArch32 ids)) M.TypeRepr)
                  => M.ArchFn ARM.AArch32 (M.Value ARM.AArch32 ids) tp
                  -> G.Generator ARM.AArch32 ids s (G.Expr ARM.AArch32 ids tp)
addArchAssignment expr = (G.ValueExpr . M.AssignedValue) <$> G.addAssignment (M.EvalArchFn expr (M.typeRepr expr))


-- | indicates that this is a placeholder type (i.e. memory or registers)
isPlaceholderType :: WT.BaseTypeRepr tp -> Bool
isPlaceholderType tp = isJust (typeAsWriteKind tp)

data WriteK = MemoryWrite | GPRWrite | SIMDWrite

typeAsWriteKind :: WT.BaseTypeRepr tp -> Maybe WriteK
typeAsWriteKind tp = case tp of
  _ | Just Refl <- testEquality tp (knownRepr :: WT.BaseTypeRepr ASL.MemoryBaseType) -> Just MemoryWrite
  _ | Just Refl <- testEquality tp (knownRepr :: WT.BaseTypeRepr ASL.AllGPRBaseType) -> Just GPRWrite
  _ | Just Refl <- testEquality tp (knownRepr :: WT.BaseTypeRepr ASL.AllSIMDBaseType) -> Just SIMDWrite
  _ -> Nothing

-- | A smart constructor for division
--
-- The smart constructor recognizes divisions that can be converted into shifts.
-- We convert the operation to a shift if the divisior is a power of two.
sdiv :: (1 <= n)
     => NatRepr n
     -> M.Value ARM.AArch32 ids (M.BVType n)
     -> M.Value ARM.AArch32 ids (M.BVType n)
     -> G.Generator ARM.AArch32 ids s (G.Expr ARM.AArch32 ids (M.BVType n))
sdiv repr dividend divisor =
  case divisor of
    M.BVValue nr val
      | bv <- BVS.mkBV repr val
      , BVS.asUnsigned (BVS.popCount bv) == 1 ->
        withKnownNat repr $
          let app = M.BVSar nr dividend (M.BVValue nr (BVS.asUnsigned (BVS.ctz repr bv)))
          in G.ValueExpr <$> G.addExpr (G.AppExpr app)
    _ -> addArchAssignment (SDiv repr dividend divisor)


mkTupT :: [TypeQ] -> Q Type
mkTupT [t] = t
mkTupT ts = foldl appT (tupleT (length ts)) ts



armTranslateType :: Q Type
                 -> Q Type
                 -> WT.BaseTypeRepr tp
                 -> Maybe (Q Type)
armTranslateType idsTy sTy tp = case tp of
  WT.BaseStructRepr reprs -> Just $ mkTupT $ FC.toListFC translateBaseType reprs
  _ | isPlaceholderType tp -> Just $ translateBaseType tp
  _ -> Nothing
  where
    translateBaseType :: forall tp'. WT.BaseTypeRepr tp' -> Q Type
    translateBaseType tp' =  case typeAsWriteKind tp' of
      Just MemoryWrite -> [t| ARMMemoryWrites $(idsTy) $(sTy) |]
      Just GPRWrite -> [t| ARMGPRWrites $(idsTy) $(sTy) |]
      Just SIMDWrite -> [t| ARMSIMDWrites $(idsTy) $(sTy) |]
      _ -> case tp' of
        WT.BaseBoolRepr -> [t| M.Value ARM.AArch32 $(idsTy) M.BoolType |]
        WT.BaseBVRepr n -> [t| M.Value ARM.AArch32 $(idsTy) (M.BVType $(litT (numTyLit (intValue n)))) |]
        _ -> fail $ "unsupported base type: " ++ show tp

extractTuple :: Int -> Int -> Q Exp
extractTuple len i = do
  nm <- newName "x"
  let pat = tupP $ [ if i' == i then varP nm else wildP | i' <- [0..len-1] ]
  lamE [pat] (varE nm)

joinTuple :: [ExpQ] -> Q Exp
joinTuple es = go [] es
  where
    go :: [Name] -> [ExpQ] -> Q Exp
    go ns (e : es') = do
      n <- newName "bval"
      [| $(e) >>= $(lamE [varP n] (go (n : ns) es')) |]
    go ns [] = [| return $(tupE $ map varE (reverse ns)) |]

refField :: Ctx.Size ctx -> Ctx.Index ctx tp -> BoundExp -> MacawQ arch t fs BoundExp
refField sz idx e = case Ctx.viewSize sz of
  Ctx.IncSize sz' | Ctx.ZeroSize <- Ctx.viewSize sz' -> return e
  _ -> case e of
    EagerBoundExp (TupE es) | Just v <- lookupInt es (Ctx.indexVal idx) -> return $ EagerBoundExp v
    EagerBoundExp _ -> bindTH [| $(extractTuple (Ctx.sizeInt sz) (Ctx.indexVal idx)) $(refEager e) |]
    LazyBoundExp _ -> letTH [| $(extractTuple (Ctx.sizeInt sz) (Ctx.indexVal idx)) <$> $(refBinding e) |]

-- | Compatibility class to handle the fact that the field for 'TupE' changed between
-- version 2.15 and 2.16 to be '[Maybe Exp]'
-- See: https://gitlab.haskell.org/ghc/ghc/-/issues/15843
class IntIndexable t a where
  lookupInt :: t -> Int -> Maybe a

instance IntIndexable [a] a where
  lookupInt l i = if i < length l then Just (l !! i) else Nothing

instance IntIndexable [Maybe a] a where
  lookupInt l i = if i < length l then l !! i else Nothing

armAppEvaluator :: M.Endianness
                -> BoundVarInterpretations ARM.AArch32 t fs
                -> WB.App (WB.Expr t) ctp
                -> Maybe (MacawQ ARM.AArch32 t fs Exp)
armAppEvaluator endianness interps elt =
    case elt of
      WB.BaseIte bt _ test t f | Just wk <- typeAsWriteKind bt -> return $ do
        -- In this case, the placeholder type indicates that
        -- expression is to be translated as a (wrapped) stateful action
        -- rather than an actual macaw term. The mux condition is therefore mapped
        -- across all of the stateful actions
        testE <- addEltTH endianness interps test
        inConditionalContext $ do
          tE <- addEltTH endianness interps t
          fE <- addEltTH endianness interps f
          case wk of
            MemoryWrite -> liftQ $ joinOp2 [| muxMemoryWrites $(refLazy testE) |] tE fE
            _ -> liftQ $ joinOp2 [| muxWriteMaps $(refLazy testE) |] tE fE
      WB.StructField struct _ _ |
          (WT.BaseStructRepr (Ctx.Empty Ctx.:> _)) <- WB.exprType struct -> Just $ do
        structE <- addEltTH endianness interps struct
        extractBound structE
      WB.StructField struct idx _ -> Just $ do
        WT.BaseStructRepr reprs <- return $ WB.exprType struct
        bnd <- lookupElt struct >>= \case
          Just bnd -> return bnd
          Nothing -> do
            bnd <- addEltTH endianness interps struct
            case isEager bnd of
              True -> do
                nms <- sequence $ FC.toListFC (\_ -> liftQ (newName "lval")) reprs
                letBindPat struct (tupP $ map varP nms, tupE $ map varE nms) (refEager bnd)
                res <- liftQ $ tupE $ map varE nms
                return $ EagerBoundExp res
              False -> return bnd
        
        fldBnd <- refField (Ctx.size reprs) idx bnd
        extractBound fldBnd
      WB.StructCtor _ (Ctx.Empty Ctx.:> e) -> Just $ do
        bnd <- addEltTH endianness interps e
        extractBound bnd

      WB.StructCtor _ flds -> Just $ do
        fldEs <- sequence $ FC.toListFC (addEltTH endianness interps) flds
        case all isEager fldEs of
          True -> liftQ $ [| return $(tupE (map refEager fldEs)) |]
          False -> liftQ $ joinTuple (map refBinding fldEs)            
            
      WB.BVSdiv w bv1 bv2 -> return $ do
        e1 <- addEltTH endianness interps bv1
        e2 <- addEltTH endianness interps bv2
        liftQ [| G.addExpr =<< $(joinOp2 [| sdiv $(natReprTH w) |] e1 e2) |]
      WB.BVUrem w bv1 bv2 -> return $ do
        e1 <- addEltTH endianness interps bv1
        e2 <- addEltTH endianness interps bv2
        liftQ [| G.addExpr =<< $(joinOp2 [| \e1E e2E -> addArchAssignment (URem $(natReprTH w) e1E e2E) |] e1 e2) |]
               
      WB.BVSrem w bv1 bv2 -> return $ do
        e1 <- addEltTH endianness interps bv1
        e2 <- addEltTH endianness interps bv2
        liftQ [| G.addExpr =<< $(joinOp2 [| \e1E e2E -> addArchAssignment (SRem $(natReprTH w) e1E e2E) |] e1 e2) |]
      WB.IntegerToBV _ _ -> return $ liftQ [| error "IntegerToBV" |]
      WB.SBVToInteger _ -> return $ liftQ [| error "SBVToInteger" |]
      WB.BaseIte bt _ test t f ->
        case bt of
          WT.BaseArrayRepr {} -> Just $ do
            -- Just return the true branch, since both true and false branches should be the memory or registers.
            void $ addEltTH endianness interps test
            et <- addEltTH endianness interps t
            void $ addEltTH endianness interps f
            extractBound et
          _ -> Nothing
      _ -> Nothing


------------------------------------

-- Lazy macaw values

data LazyValue ids s tp where
  LazyValue :: !(G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids tp)) -> LazyValue ids s tp
  EagerValue :: !(M.Value ARM.AArch32 ids tp) -> LazyValue ids s tp

refLazy :: BoundExp -> Q Exp
refLazy be = if isEager be then [| EagerValue $(refEager be) |] else [| LazyValue $(refBinding be) |]

evalLazyValue :: LazyValue ids s tp
              -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids tp)
evalLazyValue (LazyValue f) = f
evalLazyValue (EagerValue v) = return v


-- | Conditionally evaluate an action based on a lazy conditional
evalLazyWhen :: LazyValue ids s M.BoolType
             -- ^ condition to check
             -> LazyValue ids s tp
             -- ^ value to be evaluated
             -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids tp)
             -- ^ get value for the 'false' case when condition is symbolic
             -> (M.Value ARM.AArch32 ids tp -> G.Generator ARM.AArch32 ids s ())
             -- ^ evaluation function
             -> G.Generator ARM.AArch32 ids s ()
evalLazyWhen cond val default_ eval = case cond of
  EagerValue (M.BoolValue True) -> evalLazyValue val >>= eval
  EagerValue (M.BoolValue False) -> return ()
  _ -> do
    condE_ <- evalLazyValue cond
    valE <- evalLazyValue val
    old_v <- default_
    val' <- G.addExpr (G.AppExpr (M.Mux (M.typeRepr valE) condE_ valE old_v))
    eval val'

lazyIte :: LazyValue ids s M.BoolType
        -> LazyValue ids s tp
        -> LazyValue ids s tp
        -> LazyValue ids s tp
lazyIte (EagerValue (M.BoolValue b)) t f = if b then t else f
lazyIte cond valT valF = LazyValue $ do
  c <- evalLazyValue cond
  case c of
    M.BoolValue b -> if b then evalLazyValue valT else evalLazyValue valF
    _ -> do
      valTE <- evalLazyValue valT
      valFE <- evalLazyValue valF
      G.addExpr (G.AppExpr (M.Mux (M.typeRepr valTE) c valTE valFE))

lazyOr :: LazyValue ids s M.BoolType
       -> LazyValue ids s M.BoolType
       -> LazyValue ids s M.BoolType
lazyOr (EagerValue (M.BoolValue c)) b = if c then EagerValue (M.BoolValue True) else b
lazyOr a (EagerValue (M.BoolValue c)) = if c then EagerValue (M.BoolValue True) else a
lazyOr a b = LazyValue $ do
  aE <- evalLazyValue a
  case aE of
    M.BoolValue True -> return $ M.BoolValue True
    M.BoolValue False -> evalLazyValue b
    _ -> do
      bE <- evalLazyValue b
      G.addExpr (G.AppExpr (M.OrApp aE bE))

lazyAnd :: LazyValue ids s M.BoolType
        -> LazyValue ids s M.BoolType
        -> LazyValue ids s M.BoolType
lazyAnd (EagerValue (M.BoolValue c)) b = if c then b else EagerValue (M.BoolValue False)
lazyAnd a (EagerValue (M.BoolValue c)) = if c then a else EagerValue (M.BoolValue False)
lazyAnd a b = LazyValue $ do
  aE <- evalLazyValue a
  case aE of
    M.BoolValue True -> evalLazyValue b
    M.BoolValue False -> return $ M.BoolValue False
    _ -> do
      bE <- evalLazyValue b
      G.addExpr (G.AppExpr (M.AndApp aE bE))

lazyNot :: LazyValue ids s M.BoolType -> LazyValue ids s M.BoolType
lazyNot (EagerValue (M.BoolValue b)) = EagerValue (M.BoolValue (not b))
lazyNot a = LazyValue $ do
  aE <- evalLazyValue a
  G.addExpr (G.AppExpr (M.NotApp aE))
