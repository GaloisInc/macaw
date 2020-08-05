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
import           Data.Proxy
import           Data.Macaw.ARM.ARMReg
import           Data.Macaw.ARM.Arch
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.SemMC.Generator as G
import           Data.Macaw.SemMC.TH ( addEltTH, natReprTH, symFnName, translateBaseTypeRepr )
import           Data.Macaw.SemMC.TH.Monad
import qualified Data.Macaw.Types as M
import           Data.Parameterized.Some
import qualified Data.Parameterized.Vector as V
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map ( MapF )
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.NatRepr
import           GHC.TypeLits as TL
import qualified Lang.Crucible.Backend.Simple as CBS
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified SemMC.Architecture.AArch32 as ARM
import qualified SemMC.Architecture.ARM.Opcodes as ARM
import qualified What4.BaseTypes as WT
import qualified What4.Expr.Builder as WB

import qualified Language.ASL.Globals as ASL

import           Data.Macaw.ARM.Simplify ()

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
                liftQ $ joinOp3 [| setSIMD |] rgfE ridE valE
              _ -> fail "Invalid uf_simd_get"
          "uf_gpr_set" ->
            case args of
              Ctx.Empty Ctx.:> rgf Ctx.:> rid Ctx.:> val -> Just $ do
                rgfE <- addEltTH M.LittleEndian bvi rgf
                ridE <- addEltTH M.LittleEndian bvi rid
                valE <- addEltTH M.LittleEndian bvi val
                liftQ $ joinOp3 [| setGPR |] rgfE ridE valE
              _ -> fail "Invalid uf_gpr_get"
          "uf_simd_get" ->
            case args of
              Ctx.Empty Ctx.:> array Ctx.:> ix ->
                Just $ do
                  _rgf <- addEltTH M.LittleEndian bvi array
                  rid <- addEltTH M.LittleEndian bvi ix
                  liftQ $ joinOp1 [| getSIMD Snapshot |] rid
              _ -> fail "Invalid uf_simd_get"
          "uf_gpr_get" ->
            case args of
              Ctx.Empty Ctx.:> array Ctx.:> ix ->
                Just $ do
                  _rgf <- addEltTH M.LittleEndian bvi array
                  rid <- addEltTH M.LittleEndian bvi ix
                  liftQ $ joinOp1 [| getGPR Snapshot |] rid
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
                liftQ $ joinOp3 [| writeMem $(natReprFromIntTH memWidth) |] memE addrE valE
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


          "uf_init_gprs" -> Just $ liftQ [| return $ emptyGPRWrites |]
          "uf_init_memory" -> Just $ liftQ [| return $ emptyMemoryWrites |]
          "uf_init_simds" -> Just $ liftQ [| return $ emptySIMDWrites |]


          -- These functions indicate that the wrapped monadic actions in the corresponding
          -- 'ARMWriteAction' should be executed, committing their stateful actions.
          "uf_update_gprs"
            | Ctx.Empty Ctx.:> gprs <- args -> Just $ do
                gprs' <- addEltTH M.LittleEndian bvi gprs
                appendStmt $ [| join (execWriteGPRs <$> $(refBinding gprs')) |]
                liftQ [| return $ unitValue |]
                  
          "uf_update_simds"
            | Ctx.Empty Ctx.:> simds <- args -> Just $ do
                simds' <- addEltTH M.LittleEndian bvi simds
                appendStmt $ [| join (execWriteSIMDs <$> $(refBinding simds')) |]
                liftQ [| return $ unitValue |]

          "uf_update_memory"
            | Ctx.Empty Ctx.:> mem <- args -> Just $ do
                mem' <- addEltTH M.LittleEndian bvi mem
                appendStmt $ [| join (execMemoryWrites <$> $(refBinding mem')) |]
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
data WriteAction f addr val where
  -- | A single write action 
  WriteAction :: forall f addr val
               . (1 <= addr, 1 <= val)
              => M.NatRepr addr
              -> M.NatRepr val
              -> f M.BoolType
              -- ^ a guard which indicates whether or not this action should be committed
              -> f (M.BVType addr)
              -> f (M.BVType (8 TL.* val))
              -> WriteAction f addr val

-- | A sequence of a known number of write actions
data WriteSeq f addr val n where
  WriteSeq :: 1 <= n => V.Vector n (WriteAction f addr val) -> WriteSeq f addr val n
  EmptyWriteSeq :: WriteSeq f addr val 0

appendWriteSeqs :: WriteSeq f addr val n
                -> WriteSeq f addr val m
                -> WriteSeq f addr val (n + m)
appendWriteSeqs s1 s2 = case (s1, s2) of
  (EmptyWriteSeq, _) -> s2
  (_, EmptyWriteSeq) -> s1
  (WriteSeq v1, WriteSeq v2)
     | LeqProof <- leqAddPos (V.length v1) (V.length v2)
     -> WriteSeq $ V.append v1 v2

data ARMWriteActions ids addr val where
  ARMWriteActions :: WriteSeq (M.Value ARM.AArch32 ids) addr val n -> ARMWriteActions ids addr val

getValRepr :: M.Value ARM.AArch32 ids (M.BVType (8 TL.* w))
           -> NatRepr w
getValRepr val
  | M.BVTypeRepr (val8Repr :: NatRepr (8 TL.* val)) <- M.typeRepr val
  , Refl <- mulComm (Proxy @8) (Proxy @val)
  = divNat @8 @val val8Repr (knownNat @8)
getValRepr _ = error "impossible"

addWriteAction :: forall addr ids val
                . 1 <= val
               => 1 <= addr
               => M.Value ARM.AArch32 ids (M.BVType addr)
               -> M.Value ARM.AArch32 ids (M.BVType (8 TL.* val))
               -> ARMWriteActions ids addr val
               -> ARMWriteActions ids addr val
addWriteAction addr val acts = appendWriteActions (singletonWriteAction addr val) acts

emptyGPRWrites :: ARMWriteActions ids 4 4
emptyGPRWrites = ARMWriteActions EmptyWriteSeq

emptySIMDWrites :: ARMWriteActions ids 8 16
emptySIMDWrites = ARMWriteActions EmptyWriteSeq

emptyMemoryWrites :: MemoryWriteActions ids
emptyMemoryWrites = MemoryWriteActions $ MapF.empty

singletonWriteAction :: forall addr ids val
                      . 1 <= val
                     => 1 <= addr
                     => M.Value ARM.AArch32 ids (M.BVType addr)
                     -> M.Value ARM.AArch32 ids (M.BVType (8 TL.* val))
                     -> ARMWriteActions ids addr val
singletonWriteAction addr val
  | M.BVTypeRepr addrRepr <- M.typeRepr addr
  , valRepr <- getValRepr val
  , act <- WriteAction addrRepr valRepr (M.BoolValue True) addr val
  = ARMWriteActions (WriteSeq (V.singleton act))
singletonWriteAction _ _ = error "impossible"

appendWriteActions :: ARMWriteActions ids addr val
                   -> ARMWriteActions ids addr val
                   -> ARMWriteActions ids addr val
appendWriteActions (ARMWriteActions acts1) (ARMWriteActions acts2)
 = ARMWriteActions $ appendWriteSeqs acts1 acts2

-- | Zip two sequences of write actions together. The shorter of the two sequences will
-- be padded with 'Nothing' until they are equal length.
zipWriteSeqs :: Monad m
             => (Maybe (WriteAction f addr val) -> Maybe (WriteAction f addr val) -> m (WriteAction f addr val))
             -> WriteSeq f addr val n
             -> WriteSeq f addr val k
             -> m (Some (WriteSeq f addr val))
zipWriteSeqs f s1 s2 = case (s1, s2) of
  (WriteSeq v1, EmptyWriteSeq) -> (Some . WriteSeq) <$> mapM (\a -> f (Just a) Nothing) v1
  (EmptyWriteSeq, WriteSeq v2) -> (Some . WriteSeq) <$> mapM (\b -> f Nothing (Just b)) v2
  (WriteSeq v1, WriteSeq v2) -> do
    SomeVector v <- someMaxVector <$> zipWithM' f v1 v2
    return $ Some $ WriteSeq v
  _ -> return $ Some $ EmptyWriteSeq

muxWriteAction :: forall ids s addr val
                . M.Value ARM.AArch32 ids M.BoolType
               -> ARMWriteActions ids addr val
               -> ARMWriteActions ids addr val
               -> G.Generator ARM.AArch32 ids s (ARMWriteActions ids addr val)
muxWriteAction cond (ARMWriteActions actsT) (ARMWriteActions actsF) = do
  Some acts <- zipWriteSeqs (mkMux cond) actsT actsF
  return $ ARMWriteActions acts

muxMemoryWrites :: forall ids s
                 . M.Value ARM.AArch32 ids M.BoolType
                -> MemoryWriteActions ids
                -> MemoryWriteActions ids
                -> G.Generator ARM.AArch32 ids s (MemoryWriteActions ids)
muxMemoryWrites cond (MemoryWriteActions mem1) (MemoryWriteActions mem2) =
  MemoryWriteActions <$> MapF.mergeWithKeyM (\_ act1 act2 -> Just <$> muxWriteAction cond act1 act2) return return mem1 mem2

mkMux :: M.Value ARM.AArch32 ids M.BoolType
      -> Maybe (WriteAction (M.Value ARM.AArch32 ids) addr val)
      -> Maybe (WriteAction (M.Value ARM.AArch32 ids) addr val)
      -> G.Generator ARM.AArch32 ids s (WriteAction (M.Value ARM.AArch32 ids) addr val)
mkMux cond_outer mvt mvf = case (mvt, mvf) of
  (Just (WriteAction addrRepr valRepr condT addrT valT), Nothing) -> do
    cond <- G.addExpr (G.AppExpr (M.AndApp cond_outer condT))
    return $ WriteAction addrRepr valRepr cond addrT valT
  (Nothing, Just (WriteAction addrRepr valRepr condF addrF valF)) -> do
    notCond_outer <- G.addExpr (G.AppExpr (M.NotApp cond_outer))
    cond <- G.addExpr (G.AppExpr (M.AndApp notCond_outer condF))
    return $ WriteAction addrRepr valRepr cond addrF valF
  (Just (WriteAction addrRepr valRepr condT addrT valT) , Just (WriteAction _ _ condF addrF valF)) -> do
    cond <- G.addExpr (G.AppExpr (M.Mux M.BoolTypeRepr cond_outer condT condF))
    addr <- G.addExpr (G.AppExpr (M.Mux (M.typeRepr addrT) cond_outer addrT addrF))
    val <- G.addExpr (G.AppExpr (M.Mux (M.typeRepr valT) cond_outer valT valF))
    return $ WriteAction addrRepr valRepr cond addr val
  (Nothing, Nothing) -> error "mkMux: unexpected no-op action"

execWriteGPRs :: forall ids s
               . ARMWriteActions ids 4 4
              -> G.Generator ARM.AArch32 ids s ()
execWriteGPRs (ARMWriteActions (WriteSeq acts)) = mapM_ go acts
  where
    go :: WriteAction (M.Value ARM.AArch32 ids) 4 4 -> G.Generator ARM.AArch32 ids s ()
    go (WriteAction _ _ cond addr val) = case cond of
      M.CValue (M.BoolCValue True) -> execSetGPR addr val
      M.CValue (M.BoolCValue False) -> return ()
      _ -> do
        old_v <- getGPR Current addr
        val' <- G.addExpr (G.AppExpr (M.Mux (M.typeRepr val) cond val old_v))
        execSetGPR addr val'
execWriteGPRs (ARMWriteActions EmptyWriteSeq) = return ()

execWriteSIMDs :: forall ids s
                . ARMWriteActions ids 8 16
               -> G.Generator ARM.AArch32 ids s ()
execWriteSIMDs (ARMWriteActions (WriteSeq acts)) = mapM_ go acts
  where
    go :: WriteAction (M.Value ARM.AArch32 ids) 8 16 -> G.Generator ARM.AArch32 ids s ()
    go (WriteAction _ _ cond addr val) = case cond of
      M.CValue (M.BoolCValue True) -> execSetSIMD addr val
      M.CValue (M.BoolCValue False) -> return ()
      _ -> do
        old_v <- getSIMD Current addr
        val' <- G.addExpr (G.AppExpr (M.Mux (M.typeRepr val) cond val old_v))
        execSetSIMD addr val'
execWriteSIMDs (ARMWriteActions EmptyWriteSeq) = return ()

execMemoryWrites :: forall ids s
                  . MemoryWriteActions ids
                 -> G.Generator ARM.AArch32 ids s ()
execMemoryWrites (MemoryWriteActions mem) = MapF.traverseWithKey_ execW mem
  where
    execW :: forall n. NatRepr n -> ARMWriteActions ids 32 n -> G.Generator ARM.AArch32 ids s ()
    execW _ (ARMWriteActions (WriteSeq acts)) = mapM_ go acts
    execW _ (ARMWriteActions EmptyWriteSeq) = return ()

    go :: forall n. WriteAction (M.Value ARM.AArch32 ids) 32 n -> G.Generator ARM.AArch32 ids s ()
    go (WriteAction _ sz cond addr val) = case cond of
      M.CValue (M.BoolCValue True) -> execWriteMem sz addr val
      M.CValue (M.BoolCValue False) -> return ()
      _ -> do
        old_v <- readMem sz addr
        val' <- G.addExpr (G.AppExpr (M.Mux (M.typeRepr val) cond val old_v))
        execWriteMem sz addr val'


data MemoryWriteActions ids where
  MemoryWriteActions :: MapF NatRepr (ARMWriteActions ids 32) -> MemoryWriteActions ids


writeMem :: 1 <= w
         => M.NatRepr w
         -> MemoryWriteActions ids
         -> M.Value ARM.AArch32 ids (M.BVType 32)
         -> M.Value ARM.AArch32 ids (M.BVType (8 TL.* w))
         -> G.Generator ARM.AArch32 ids s (MemoryWriteActions ids)
writeMem sz (MemoryWriteActions mem) addr val =
  return $ MemoryWriteActions $ MapF.insertWith appendWriteActions sz (singletonWriteAction addr val) mem


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


setGPR :: ARMWriteActions ids 4 4
       -> M.Value ARM.AArch32 ids (M.BVType 4)
       -> M.Value ARM.AArch32 ids (M.BVType 32)
       -> G.Generator ARM.AArch32 ids s (ARMWriteActions ids 4 4)
setGPR acts regid v = return $ addWriteAction regid v acts

data AccessMode = Current | Snapshot

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

setSIMD :: ARMWriteActions ids 8 16
        -> M.Value ARM.AArch32 ids (M.BVType 8)
        -> M.Value ARM.AArch32 ids (M.BVType 128)
        -> G.Generator ARM.AArch32 ids s (ARMWriteActions ids 8 16)
setSIMD acts regid v = return $ addWriteAction regid v acts


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
armTranslateType idsTy _ tp = case tp of
  WT.BaseStructRepr reprs -> Just $ mkTupT $ FC.toListFC translateBaseType reprs
  _ | isPlaceholderType tp -> Just $ translateBaseType tp
  _ -> Nothing
  where
    translateBaseType :: forall tp'. WT.BaseTypeRepr tp' -> Q Type
    translateBaseType tp' =  case typeAsWriteKind tp' of
      Just MemoryWrite -> [t| MemoryWriteActions $(idsTy) |]
      Just GPRWrite -> [t| ARMWriteActions $(idsTy) 4 4 |]
      Just SIMDWrite -> [t| ARMWriteActions $(idsTy) 8 16 |]
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
    EagerBoundExp (TupE es) | Ctx.indexVal idx < length es -> return $ EagerBoundExp $ es !! (Ctx.indexVal idx)
    EagerBoundExp _ -> bindTH [| $(extractTuple (Ctx.sizeInt sz) (Ctx.indexVal idx)) $(refEager e) |]
    LazyBoundExp _ -> letTH [| $(extractTuple (Ctx.sizeInt sz) (Ctx.indexVal idx)) <$> $(refBinding e) |]

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
        tE <- addEltTH endianness interps t
        fE <- addEltTH endianness interps f
        case wk of
          MemoryWrite -> liftQ $ joinOp3 [| muxMemoryWrites |] testE tE fE
          _ -> liftQ $ joinOp3 [| muxWriteAction |] testE tE fE
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

-- General vector functions

-- | Pad a vector with a tail of 'Nothing' to match a given size
padVector :: forall k n a
          . 1 <= k
         => 1 <= n
         => n <= k
         => M.NatRepr k
         -> V.Vector n a
         -> V.Vector k (Maybe a)
padVector k v = case testStrictLeq (V.length v) k of
  Right Refl -> fmap Just v
  Left n_lt_k
    | Refl <- minusPlusCancel k (knownNat @1)
    , n <- V.length v
    , Refl <- plusMinusCancel n (knownNat @1)
    , Refl <- plusMinusCancel (knownNat @1) n 
    , one_le_one <- leqProof (knownNat @1) (knownNat @1)
    , one_le_n <- leqProof (knownNat @1) n
    , Refl <- plusComm (knownNat @1) n
    , LeqProof :: LeqProof 1 (k-1) <- leqSub2 n_lt_k one_le_n
    , LeqProof :: LeqProof n (k-1) <- leqSub2 n_lt_k one_le_one
    , padded <- padVector (decNat k) v
    -> V.snoc padded Nothing

data MaxVector n k a where
  MaxVector1 :: (1 <= k, n <= k) => V.Vector k a -> MaxVector n k a
  MaxVector2 :: (1 <= n, k <= n) => V.Vector n a -> MaxVector n k a

data SomeVector a where
  SomeVector :: 1 <= n => V.Vector n a -> SomeVector a

someMaxVector :: MaxVector n k a -> SomeVector a
someMaxVector mv = case mv of
  MaxVector1 v -> SomeVector v
  MaxVector2 v -> SomeVector v

-- | Zip two mismatched vectors, producing a vector which is the larger of the two sizes
zipWithM' :: 1 <= n
          => 1 <= k
          => Monad m
          => (Maybe a -> Maybe b -> m c)
          -> V.Vector n a
          -> V.Vector k b
          -> m (MaxVector n k c)
zipWithM' f v1 v2
  | n :: NatRepr n <- V.length v1
  , k :: NatRepr k <- V.length v2
  = case testNatCases n k of
      NatCaseLT prf
        | LeqProof <- addIsLeqLeft1 @n @1 prf
        -> MaxVector1 <$> V.zipWithM f (padVector (V.length v2) v1) (fmap Just v2)
      NatCaseEQ -> MaxVector1 <$> V.zipWithM f (fmap Just v1) (fmap Just v2)
      NatCaseGT prf
        | LeqProof <-  addIsLeqLeft1 @k @1 prf
        -> MaxVector2 <$> V.zipWithM f (fmap Just v1) (padVector (V.length v1) v2)
