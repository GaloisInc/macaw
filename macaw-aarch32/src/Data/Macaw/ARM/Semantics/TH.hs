{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveLift #-}
module Data.Macaw.ARM.Semantics.TH
    ( armAppEvaluator
    , armNonceAppEval
    , getGPR
    , setGPR
    , getSIMD
    , setSIMD
    , loadSemantics
    )
    where

import           Control.Monad (void)
import qualified Control.Monad.Except as E
import qualified Data.BitVector.Sized as BVS
import qualified Data.Bits as B
import           Data.List (isPrefixOf)
import           Data.Macaw.ARM.ARMReg
import           Data.Macaw.ARM.Arch
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.SemMC.Generator as G
import           Data.Macaw.SemMC.TH ( addEltTH, appToExprTH, evalNonceAppTH, evalBoundVar, natReprTH, symFnName, bindTH )
import           Data.Macaw.SemMC.TH.Monad
import qualified Data.Macaw.Types as M
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
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
          "uf_simd_set" ->
            case args of
              Ctx.Empty Ctx.:> rgf Ctx.:> rid Ctx.:> val -> Just $ do
                rgfE <- addEltTH M.LittleEndian bvi rgf
                ridE <- addEltTH M.LittleEndian bvi rid
                valE <- addEltTH M.LittleEndian bvi val
                bindTH [| setSIMD $(return rgfE) $(return ridE) $(return valE) |]
              _ -> fail "Invalid uf_simd_get"
          "uf_gpr_set" ->
            case args of
              Ctx.Empty Ctx.:> rgf Ctx.:> rid Ctx.:> val -> Just $ do
                rgfE <- addEltTH M.LittleEndian bvi rgf
                ridE <- addEltTH M.LittleEndian bvi rid
                valE <- addEltTH M.LittleEndian bvi val
                bindTH [| setGPR $(return rgfE) $(return ridE) $(return valE) |]
              _ -> fail "Invalid uf_gpr_get"
          "uf_simd_get" ->
            case args of
              Ctx.Empty Ctx.:> array Ctx.:> ix ->
                Just $ do
                  _rgf <- addEltTH M.LittleEndian bvi array
                  rid <- addEltTH M.LittleEndian bvi ix
                  bindTH [| getSIMD $(return rid) |]
              _ -> fail "Invalid uf_simd_get"
          "uf_gpr_get" ->
            case args of
              Ctx.Empty Ctx.:> array Ctx.:> ix ->
                Just $ do
                  _rgf <- addEltTH M.LittleEndian bvi array
                  rid <- addEltTH M.LittleEndian bvi ix
                  bindTH [| getGPR $(return rid) |]
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
                bindTH [| writeMem $(return memE) $(return addrE) $(natReprFromIntTH memWidth) $(return valE) |]
              _ -> fail "invalid write_mem"

          "uf_init_gprs" -> Just $ bindTH [| M.AssignedValue <$> G.addAssignment (M.SetUndefined $(what4TypeTH tp)) |]
          "uf_init_memory" -> Just $ bindTH [| M.AssignedValue <$> G.addAssignment (M.SetUndefined $(what4TypeTH tp)) |]
          "uf_init_simds" -> Just $ bindTH [| M.AssignedValue <$> G.addAssignment (M.SetUndefined $(what4TypeTH tp)) |]
          "uf_update_gprs"
            | Ctx.Empty Ctx.:> gprs <- args -> Just $ do
              appendStmt [| setWriteMode WriteGPRs |]
              gprs' <- addEltTH M.LittleEndian bvi gprs
              appendStmt [| setWriteMode WriteNone |]
              bindTH [| return $(return gprs') |]
              
          "uf_update_simds"
            | Ctx.Empty Ctx.:> simds <- args -> Just $ do
              appendStmt [| setWriteMode WriteSIMDs |]
              simds' <- addEltTH M.LittleEndian bvi simds
              appendStmt [| setWriteMode WriteNone |]
              bindTH [| return $(return simds') |]
          "uf_update_memory"
            | Ctx.Empty Ctx.:> mem <- args -> Just $ do
              appendStmt [| setWriteMode WriteMemory |]
              mem' <- addEltTH M.LittleEndian bvi mem
              appendStmt [| setWriteMode WriteNone |]
              bindTH [| return $(return mem') |]
          _ | "uf_assertBV_" `isPrefixOf` fnName ->
            case args of
              Ctx.Empty Ctx.:> assert Ctx.:> bv -> Just $ do
                assertTH <- addEltTH M.LittleEndian bvi assert
                bvElt <- addEltTH M.LittleEndian bvi bv
                liftQ [| case $(return assertTH) of
                          M.BoolValue True -> return $(return bvElt)
                          M.BoolValue False -> E.throwError (G.GeneratorMessage $ "Bitvector length assertion failed!")
                          -- FIXME: THIS SHOULD THROW AN ERROR
                          _ -> return $(return bvElt)
                          -- nm -> E.throwError (G.GeneratorMessage $ "Bitvector length assertion failed: <FIXME: PRINT NAME>")
                       |]
              _ -> fail "Invalid call to assertBV"

          _ | "uf_UNDEFINED_" `isPrefixOf` fnName ->
               Just $ bindTH [| M.AssignedValue <$> G.addAssignment (M.SetUndefined $(what4TypeTH tp)) |]
          _ | "uf_INIT_GLOBAL_" `isPrefixOf` fnName ->
               Just $ bindTH [| M.AssignedValue <$> G.addAssignment (M.SetUndefined $(what4TypeTH tp)) |]
          _ -> Nothing
      _ -> Nothing -- fallback to default handling

natReprFromIntTH :: Int -> Q Exp
natReprFromIntTH i = [| knownNat :: M.NatRepr $(litT (numTyLit (fromIntegral i))) |]

data WriteMode =
  WriteNone
  | WriteGPRs
  | WriteSIMDs
  | WriteMemory
  deriving (Show, Eq, Lift)

getWriteMode :: G.Generator ARM.AArch32 ids s WriteMode
getWriteMode = do
  G.getRegVal ARMWriteMode >>= \case
      M.BVValue _ i -> return $ case i of
        0 -> WriteNone
        1 -> WriteGPRs
        2 -> WriteSIMDs
        3 -> WriteMemory
        _ -> error "impossible"
      _ -> error "impossible"
        
setWriteMode :: WriteMode -> G.Generator ARM.AArch32 ids s ()
setWriteMode wm =
  let
    i = case wm of
      WriteNone -> 0
      WriteGPRs -> 1
      WriteSIMDs -> 2
      WriteMemory -> 3
  in G.setRegVal ARMWriteMode (M.BVValue knownNat i)

writeMem :: 1 <= w
         => M.Value ARM.AArch32 ids tp
         -> M.Value ARM.AArch32 ids (M.BVType 32)
         -> M.NatRepr w
         -> M.Value ARM.AArch32 ids (M.BVType (8 TL.* w))
         -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids tp)
writeMem mem addr sz val = do
  wm <- getWriteMode
  case wm of
    WriteMemory -> do
      G.addStmt (M.WriteMem addr (M.BVMemRepr sz M.LittleEndian) val)
      return mem
    _ -> return mem
                                 
setGPR :: M.Value ARM.AArch32 ids tp
       -> M.Value ARM.AArch32 ids (M.BVType 4)
       -> M.Value ARM.AArch32 ids (M.BVType 32)
       -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids tp)
setGPR handle regid v = do
  reg <- case regid of
    M.BVValue w i
      | intValue w == 4
      , Just reg <- integerToReg i -> return reg
    _ -> E.throwError (G.GeneratorMessage $ "Bad GPR identifier (uf_gpr_set): " <> show (M.ppValueAssignments v))
  getWriteMode >>= \case
    WriteGPRs -> G.setRegVal reg v
    _ -> return ()
  return handle

getGPR :: M.Value ARM.AArch32 ids tp 
       -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids (M.BVType 32))
getGPR v = do
  reg <- case v of
    M.BVValue w i
      | intValue w == 4
      , Just reg <- integerToReg i -> return reg
    _ ->  E.throwError (G.GeneratorMessage $ "Bad GPR identifier (uf_gpr_get): " <> show (M.ppValueAssignments v))
  G.getRegSnapshotVal reg

setSIMD :: M.Value ARM.AArch32 ids tp
       -> M.Value ARM.AArch32 ids (M.BVType 8)
       -> M.Value ARM.AArch32 ids (M.BVType 128)
       -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids tp)
setSIMD handle regid v = do
  reg <- case regid of
    M.BVValue w i
      | intValue w == 8
      , Just reg <- integerToSIMDReg i -> return reg
    _ -> E.throwError (G.GeneratorMessage $ "Bad SIMD identifier (uf_simd_set): " <> show (M.ppValueAssignments v))
  getWriteMode >>= \case
    WriteSIMDs -> G.setRegVal reg v
    _ -> return ()
  return handle

getSIMD :: M.Value ARM.AArch32 ids tp 
       -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids (M.BVType 128))
getSIMD v = do
  reg <- case v of
    M.BVValue w i
      | intValue w == 8
      , Just reg <- integerToSIMDReg i -> return reg
    _ ->  E.throwError (G.GeneratorMessage $ "Bad SIMD identifier (uf_simd_get): " <> show (M.ppValueAssignments v))
  G.getRegVal reg

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


-- | indicates that this is a placeholder type (i.e. memory or registers)
isPlaceholderType :: WT.BaseTypeRepr tp -> Bool
isPlaceholderType tp = case tp of
  _ | Just Refl <- testEquality tp (knownRepr :: WT.BaseTypeRepr ASL.MemoryBaseType) -> True
  _ | Just Refl <- testEquality tp (knownRepr :: WT.BaseTypeRepr ASL.AllGPRBaseType) -> True
  _ | Just Refl <- testEquality tp (knownRepr :: WT.BaseTypeRepr ASL.AllSIMDBaseType) -> True
  _ -> False

translateExpr :: M.Endianness
              -> BoundVarInterpretations ARM.AArch32 t fs
              -> WB.Expr t tp
              -> MacawQ ARM.AArch32 t fs Exp
translateExpr endianness interps e = case e of
  WB.AppExpr app -> do
    x <- appToExprTH endianness (WB.appExprApp app) interps
    bindExpr e [| return $(return x) |]
  WB.BoundVarExpr bvar -> do
    val <- evalBoundVar interps bvar
    liftQ [| $(return val) |]
  WB.NonceAppExpr n -> do
    val <- evalNonceAppTH endianness interps (WB.nonceExprApp n)
    liftQ [| $(return val) |]
  _ -> fail $ "translateExpr: unexpected expression kind: " ++ show e

-- | This combinator provides conditional evaluation of its branches
--
-- Many conditionals in the semantics are translated as muxes (effectively
-- if-then-else expressions).  This is great most of the time, but problematic
-- if the branches include side effects (e.g., memory writes).  We only want
-- side effects to happen if the condition really is true.
--
-- This combinator checks to see if the condition is concretely true or false
-- (as expected) and then evaluates the corresponding 'G.Generator' action.
--
-- It is meant to be used in a context like:
--
-- > val <- concreteIte condition trueThings falseThings
--
-- where @condition@ has type Value and the branches have type 'G.Generator'
-- 'M.Value' (i.e., the branches get to return a value).
--
-- NOTE: This function panics (and throws an error) if the argument is not
-- concrete.
concreteIte :: M.Value ARM.AArch32 ids (M.BoolType)
            -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids tp)
            -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids tp)
            -> G.Generator ARM.AArch32 ids s (M.Value ARM.AArch32 ids tp)
concreteIte v t f = case v of
  M.CValue (M.BoolCValue b) -> if b then t else f
  _ ->  E.throwError (G.GeneratorMessage $ "concreteIte: requires concrete value" <> show (M.ppValueAssignments v))

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
      | bv <- BVS.bitVector' repr val
      , BVS.bvPopCount bv == 1 ->
        withKnownNat repr $
          let app = M.BVSar nr dividend (M.BVValue nr (fromIntegral (B.countTrailingZeros bv)))
          in G.ValueExpr <$> G.addExpr (G.AppExpr app)
    _ -> addArchAssignment (SDiv repr dividend divisor)

armAppEvaluator :: M.Endianness
                -> BoundVarInterpretations ARM.AArch32 t fs
                -> WB.App (WB.Expr t) ctp
                -> Maybe (MacawQ ARM.AArch32 t fs Exp)
armAppEvaluator endianness interps elt =
    case elt of
      WB.BaseIte bt _ test t f | isPlaceholderType bt -> return $ do
        testE <- addEltTH endianness interps test
        -- tE <- inLocalBlock (addEltTH endianness interps t)
        -- fE <- inLocalBlock (addEltTH endianness interps f)
        tE <- translateExpr endianness interps t
        fE <- translateExpr endianness interps f
        bindTH [| concreteIte $(return testE) (return $(return tE)) (return $(return fE)) |]
      WB.BVSdiv w bv1 bv2 -> return $ do
        e1 <- addEltTH endianness interps bv1
        e2 <- addEltTH endianness interps bv2
        bindTH [| G.addExpr =<< sdiv $(natReprTH w) $(return e1) $(return e2) |]
      WB.BVUrem w bv1 bv2 -> return $ do
        e1 <- addEltTH endianness interps bv1
        e2 <- addEltTH endianness interps bv2
        bindTH [| G.addExpr =<< addArchAssignment (URem $(natReprTH w) $(return e1) $(return e2))
               |]
      WB.BVSrem w bv1 bv2 -> return $ do
        e1 <- addEltTH endianness interps bv1
        e2 <- addEltTH endianness interps bv2
        bindTH [| G.addExpr =<< addArchAssignment (SRem $(natReprTH w) $(return e1) $(return e2))
               |]
      WB.IntegerToBV _ _ -> return $ liftQ [| error "IntegerToBV" |]
      WB.SBVToInteger _ -> return $ liftQ [| error "SBVToInteger" |]
      WB.BaseIte bt _ test t f -> 
        case bt of
          WT.BaseArrayRepr {} -> Just $ do
            -- Just return the true branch, since both true and false branches should be the memory or registers.
            void $ addEltTH endianness interps test
            et <- addEltTH endianness interps t
            void $ addEltTH endianness interps f
            return et
            -- liftQ $ [| G.ValueExpr $(return et) |]
            -- liftQ [| G.ValueExpr <$> M.AssignedValue <$> G.addAssignment (M.SetUndefined (M.TupleTypeRepr L.Nil)) |]
          _ -> Nothing
      _ -> Nothing
