{-# OPTIONS_GHC -ddump-splices -ddump-to-file #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiWayIf #-}
-- | Architecture-independent translation of semmc semantics (via SimpleBuilder)
-- into macaw IR.
--
-- The main entry point is 'genExecInstruction', which is customized for
-- architecture-specific backends via some parameters.
--
-- The other functions exposed by this module are useful for implementing
-- architecture-specific translations.

module Data.Macaw.SemMC.TH (
  MacawTHConfig(..),
  MacawSemMC(..),
  Sym,
  genExecInstruction,
  genExecInstructionLogStdErr,
  genExecInstructionLogging,
  addEltTH,
  bindTH,
  appToExprTH,
  evalNonceAppTH,
  evalBoundVar,
  natReprTH,
  floatInfoTH,
  floatInfoFromPrecisionTH,
  symFnName,
  asName,
  translateBaseType,
  translateBaseTypeRepr
  ) where

import           GHC.TypeLits ( Symbol )

import           Control.Lens ( (^.) )
import           Control.Monad ( ap, join, void, liftM, foldM, forM )
import qualified Control.Concurrent.Async as Async
import qualified Data.Functor.Const as C
import           Data.Functor.Product
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Kind as DK
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as T
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified LibBF as BF
import           Text.Read ( readMaybe )

import qualified Data.BitVector.Sized as BVS
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.HasRepr as HR
import qualified Data.Parameterized.Lift as LF
import qualified Data.Parameterized.List as SL
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Pair as Pair
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC

import qualified What4.BaseTypes as CT
import qualified What4.Expr.BoolMap as BooM
import qualified What4.Expr.Builder as S
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Interface as SI
import qualified What4.InterpretedFloatingPoint as SI
import qualified What4.SemiRing as SR
import qualified What4.Symbol as Sy

import qualified Dismantle.Instruction as D
import qualified Dismantle.Tablegen.TH.Capture as DT

import qualified SemMC.BoundVar as BV
import           SemMC.Formula
import qualified SemMC.Architecture as A
import qualified SemMC.Architecture.Location as L
import qualified Data.Macaw.SemMC.Simplify as MSS
import qualified SemMC.Util as U
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.Symbolic as M

import Data.Parameterized.NatRepr ( knownNat
                                  , intValue
                                  , natValue
                                  )

import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Operands as O
import qualified Data.Macaw.SemMC.Translations as TR
import           Data.Macaw.SemMC.TH.Monad

-- | Generate the top-level lambda with a case expression over an instruction
-- (casing on opcode)
--
-- > \ipVar (Instruction opcode operandList) ->
-- >   case opcode of
-- >     ${CASES}
--
-- where each case in ${CASES} is defined by 'mkSemanticsCase'; each case
-- matches one opcode.
instructionMatcher :: forall opc arch t fs
                    . (OrdF opc, LF.LiftF opc, A.Architecture arch, ShowF opc)
                   => MacawTHConfig arch opc t fs
                   -> Library (Sym t fs)
                   -> MapF.MapF opc (Product (ParameterizedFormula (Sym t fs) arch) (DT.CaptureInfo opc))
                   -> Q (Exp, [Dec])
instructionMatcher thConf lib formulas = do
  ipVarName <- newName "_ipVal"
  opcodeVar <- newName "opcode"
  operandListVar <- newName "operands"
  (libDefs, df) <- libraryDefinitions thConf lib
  let fs = filter (\(Pair.Pair opc _) -> genOpcodeCase thConf opc) $ MapF.toList formulas
  (normalCases, bodyDefs) <- unzip <$> mapM (mkSemanticsCase thConf df ipVarName operandListVar) fs
  (fallthruNm, unimp) <- unimplementedInstruction
  fallthroughCase <- match wildP (normalB (appE (varE fallthruNm) (varE opcodeVar))) []
  let allCases :: [Match]
      allCases = concat [ normalCases
                        , [fallthroughCase]
                        ]
  instrVar <- newName "i"
  instrArg <- asP instrVar [p| D.Instruction $(varP opcodeVar) $(varP operandListVar) |]
  matcherRes <- appE (varE (instructionMatchHook thConf)) (varE instrVar)
  actionVar <- newName "action"
  let fullDefs = libDefs ++ concatMap (\(t,i) -> [t,i]) bodyDefs
  let instrCase = LetE [unimp] $ CaseE (VarE opcodeVar) allCases
  let lam = LamE [(VarP ipVarName), instrArg] $
         CaseE matcherRes
                   [ Match (conPCompat 'Just [VarP actionVar])
                               (NormalB $ AppE (ConE 'Just) (VarE actionVar)) []
                   , Match (conPCompat 'Nothing [])
                               (NormalB instrCase) []
                   ]
  return (lam, fullDefs)

-- | Unimplemented instructions return Nothing here, which will be translated
-- into a TranslationError inside the generator.
unimplementedInstruction :: Q (Name, Dec)
unimplementedInstruction = do
    fname <- newName "noMatch"
    arg1Nm <- newName "unknownOpcode"
    fdecl <- funD fname [clause [varP arg1Nm] (normalB [| Nothing |]) []]
    return (fname, fdecl)


-- | Create a function declaration for each function in the library.
-- Generates the declarations and a lookup function to use to generate
-- calls.
libraryDefinitions :: forall arch opc t fs . A.Architecture arch
                   => MacawTHConfig arch opc t fs
                   -> Library (Sym t fs)
                   -> Q ([Dec], String -> Maybe (MacawQ arch t fs Exp))
libraryDefinitions thConf lib = do
  -- First, construct map for all function names
  let ffs = MapF.elems lib
  varMap :: Map.Map String Name <- Map.fromList <$> traverse fnName ffs

  -- Create lookup functions for names and calls
  let lookupVarName name = Map.lookup name varMap
      lookupCall name = (liftQ . varE) <$> lookupVarName name
      libFuns = filter (genLibraryFunction thConf) $ MapF.elems lib
  decs <- traverse (translate lookupVarName lookupCall) libFuns
  return (concat decs, lookupCall)
  where
    fnName :: Some (FunctionFormula (Sym t fs)) -> Q (String, Name)
    fnName (Some (FunctionFormula { ffName = name })) = do
      var <- newName ("_df_" ++ name)
      return (name, var)

    translate :: (String -> Maybe Name)
              -> (String -> Maybe (MacawQ arch t fs Exp))
              -> Some (FunctionFormula (Sym t fs))
              -> Q [Dec]
    translate lookupVarName lookupCall (Some ff@(FunctionFormula {})) = do
      (_var, sig, def) <- translateFunction thConf lookupVarName lookupCall ff
      return [sig, def]

-- | Generate a single case for one opcode of the case expression.
-- Generates two parts: the case match, which calls a function to
-- handle the match, and the function definition for handling the
-- match (inlining the function body would create a more complicated
-- case expression which makes GHC much slower).
--
-- > ADD4 -> bodyfun operands
-- >
-- > bodyfun operands = ${BODY}
--
-- where the ${BODY} is generated by 'mkOperandListCase'
mkSemanticsCase :: (LF.LiftF opc, A.Architecture arch, ShowF opc)
                => MacawTHConfig arch opc t fs
                -> (String -> Maybe (MacawQ arch t fs Exp))
                -> Name
                -> Name
                -> MapF.Pair opc (Product (ParameterizedFormula (Sym t fs) arch) (DT.CaptureInfo opc))
                -> Q (Match, (Dec, Dec))
mkSemanticsCase thConf df ipVarName operandListVar (MapF.Pair opc (Pair semantics capInfo)) =
    do arg1Nm <- newName "operands"
       ofname <- newName $ "opc_" <> (filter ((/=) '"') $ nameBase $ DT.capturedOpcodeName capInfo)
       lTypeVar <- newName "l"
       idsTypeVar <- newName "ids"
       sTypeVar <- newName "s"
       ofsig <- sigD ofname [t|   (M.RegisterInfo (M.ArchReg $(archTypeQ thConf)), U.HasCallStack)
                                  => M.Value $(archTypeQ thConf) $(varT idsTypeVar) (M.BVType (M.ArchAddrWidth $(archTypeQ thConf)))
                                  -> SL.List $(operandTypeQ thConf) $(varT lTypeVar)
                                  -> Maybe (G.Generator $(archTypeQ thConf)
                                                        $(varT idsTypeVar)
                                                        $(varT sTypeVar) ())
                              |]
       ofdef <- funD ofname
                 [clause [varP ipVarName, varP arg1Nm]
                  (normalB (mkOperandListCase thConf df ipVarName arg1Nm opc semantics capInfo))
                  []]
       mtch <- match (conP (DT.capturedOpcodeName capInfo) []) (normalB (appE (appE (varE ofname) (varE ipVarName)) (varE operandListVar))) []
       return (mtch, (ofsig, ofdef))


-- | For each opcode case, we have a sub-case expression to destructure the
-- operand list into names that we can reference.  This generates an expression
-- of the form:
--
-- > case operandList of
-- >   op1 :> op2 :> op3 :> Nil -> ${BODY}
--
-- where ${BODY} is generated by 'genCaseBody', which references the operand
-- names introduced by this case (e.g., op1, op2, op3).  Those names are pulled
-- from the DT.CaptureInfo, and have been pre-allocated.  See
-- Dismantle.Tablegen.TH.Capture.captureInfo for information on how those names
-- are generated.
--
-- Note that the structure of the operand list is actually a little more
-- complicated than the above.  Each operand actually has an additional level of
-- wrapper around it, and really looks like:
--
-- >    Dismantle.PPC.ADD4
-- >      -> case operands_ayaa of {
-- >           (Gprc gprc0 :> (Gprc gprc1 :> (Gprc gprc2 :> Nil)))
-- >             -> ${BODY}
--
-- in an example with three general purpose register operands.
mkOperandListCase :: (A.Architecture arch)
                  => MacawTHConfig arch opc t fs
                  -> (String -> Maybe (MacawQ arch t fs Exp))
                  -> Name
                  -> Name
                  -> opc tp
                  -> ParameterizedFormula (Sym t fs) arch tp
                  -> DT.CaptureInfo opc tp
                  -> Q Exp
mkOperandListCase thConf df ipVarName operandListVar opc semantics capInfo = do
  body <- genCaseBody thConf df ipVarName opc semantics (DT.capturedOperandNames capInfo)
  DT.genCase capInfo operandListVar body

-- | This is the function that translates formulas (semantics) into expressions
-- that construct macaw terms.
--
-- The stub implementation is essentially
--
-- > undefined ipVar arg1 arg2
--
-- to avoid unused variable warnings.
--
-- The two maps (locVars and opVars) are crucial for translating parameterized
-- formulas into expressions.
genCaseBody :: forall opc sh t fs arch
             . (A.Architecture arch)
            => MacawTHConfig arch opc t fs
            -> (String -> Maybe (MacawQ arch t fs Exp))
            -> Name
            -> opc sh
            -> ParameterizedFormula (Sym t fs) arch sh
            -> SL.List (C.Const Name) sh
            -> Q Exp
genCaseBody thConf df ipVarName _opc semantics varNames = do
  regsName <- newName "_regs"
  translateFormula thConf df ipVarName semantics (BoundVarInterpretations locVarsMap opVarsMap argVarsMap regsName) varNames
  where
    locVarsMap :: MapF.MapF (SI.BoundVar (Sym t fs)) (L.Location arch)
    locVarsMap = MapF.foldrWithKey (collectVarForLocation (Proxy @arch)) MapF.empty (pfLiteralVars semantics)

    opVarsMap :: MapF.MapF (SI.BoundVar (Sym t fs)) (C.Const Name)
    opVarsMap = SL.ifoldr (collectOperandVars varNames) MapF.empty (pfOperandVars semantics)

    argVarsMap :: MapF.MapF (SI.BoundVar (Sym t fs)) (C.Const Name)
    argVarsMap = MapF.empty

collectVarForLocation :: forall tp arch proxy t fs
                       . proxy arch
                      -> L.Location arch tp
                      -> SI.BoundVar (Sym t fs) tp
                      -> MapF.MapF (SI.BoundVar (Sym t fs)) (L.Location arch)
                      -> MapF.MapF (SI.BoundVar (Sym t fs)) (L.Location arch)
collectVarForLocation _ loc bv = MapF.insert bv loc

-- | Index variables that map to operands
--
-- We record the TH 'Name' for the 'SI.BoundVar' that stands in for each
-- operand.  The idea will be that we will look up bound variables in this map
-- to be able to compute a TH expression to refer to it.
--
-- We have to unwrap and rewrap the 'C.Const' because the type parameter
-- changes when we switch from 'BV.BoundVar' to 'SI.BoundVar'.  See the
-- SemMC.BoundVar module for information about the nature of that change
-- (basically, from 'Symbol' to BaseType).
collectOperandVars :: forall sh tp arch t fs
                    . SL.List (C.Const Name) sh
                   -> SL.Index sh tp
                   -> BV.BoundVar (Sym t fs) arch tp
                   -> MapF.MapF (SI.BoundVar (Sym t fs)) (C.Const Name)
                   -> MapF.MapF (SI.BoundVar (Sym t fs)) (C.Const Name)
collectOperandVars varNames ix (BV.BoundVar bv) m =
  case varNames SL.!! ix of
    C.Const name -> MapF.insert bv (C.Const name) m

-- | Wrapper for 'genExecInstructionLogging' which generates a no-op
-- LogCfg to disable any logging during the generation.
genExecInstruction :: forall arch (opc :: [Symbol] -> DK.Type) (proxy :: DK.Type -> DK.Type) t fs
                    . (A.Architecture arch,
                       HR.HasRepr opc (A.ShapeRepr arch),
                       OrdF opc,
                       ShowF opc,
                       LF.LiftF opc)
                   => proxy arch
                   -> MacawTHConfig arch opc t fs
                   -> MapF.MapF opc (ParameterizedFormula (Sym t fs) arch)
                   -- ^ A list of opcodes (with constraint information
                   -- witnessed) paired with the bytestrings containing their
                   -- semantics.  This comes from semmc.
                   -> [Some (DT.CaptureInfo opc)]
                   -- ^ Extra information for each opcode to let us generate
                   -- some TH to match them.  This comes from the semantics
                   -- definitions in semmc.
                   -> Library (Sym t fs)
                   -- ^ A list of defined function names paired with the
                   -- bytestrings containing their definitions.
                   -> Q Exp
genExecInstruction proxy thConf semantics captureInfo functions = do
  logCfg <- runIO $ U.mkNonLogCfg
  (r, decs) <- genExecInstructionLogging proxy thConf semantics captureInfo functions logCfg
  runIO $ U.logEndWith logCfg
  addTopDecls decs
  return r

-- | Wrapper for 'genExecInstructionLogging' which generates a no-op
-- LogCfg to disable any logging during the generation.
genExecInstructionLogStdErr :: forall arch (opc :: [Symbol] -> DK.Type) (proxy :: DK.Type -> DK.Type) t fs
                    . (A.Architecture arch,
                       HR.HasRepr opc (A.ShapeRepr arch),
                       OrdF opc,
                       ShowF opc,
                       LF.LiftF opc)
                   => proxy arch
                   -> MacawTHConfig arch opc t fs
                   -> MapF.MapF opc (ParameterizedFormula (Sym t fs) arch)
                   -- ^ A list of opcodes (with constraint information
                   -- witnessed) paired with the bytestrings containing their
                   -- semantics.  This comes from semmc.
                   -> [Some (DT.CaptureInfo opc)]
                   -- ^ Extra information for each opcode to let us generate
                   -- some TH to match them.  This comes from the semantics
                   -- definitions in semmc.
                   -> Library (Sym t fs)
                   -- ^ A list of defined function names paired with the
                   -- bytestrings containing their definitions.
                   -> Q Exp
genExecInstructionLogStdErr proxy thConf semantics captureInfo functions = do
  logCfg <- runIO $ U.mkLogCfg "genExecInstruction"
  logThread <- runIO $ U.asyncLinked (U.stdErrLogEventConsumer (const True) logCfg)
  (r, decs) <- genExecInstructionLogging proxy thConf semantics captureInfo functions logCfg
  runIO $ U.logEndWith logCfg
  runIO $ Async.wait logThread
  addTopDecls decs
  return r

-- | Generate an implementation of 'execInstruction' that runs in the
-- 'G.Generator' monad.  We pass in both the original list of semantics files
-- along with the list of opcode info objects.  We can match them up using
-- equality on opcodes (via a MapF).  Generating a combined list up-front would
-- be ideal, but is difficult for various TH reasons (we can't call 'lift' on
-- all of the things we would need to for that).
--
-- The structure of the term produced is documented in 'instructionMatcher'
genExecInstructionLogging :: forall arch (opc :: [Symbol] -> DK.Type) (proxy :: DK.Type -> DK.Type) t fs
                             . (A.Architecture arch,
                                HR.HasRepr opc (A.ShapeRepr arch),
                                OrdF opc,
                                ShowF opc,
                                LF.LiftF opc)
                   => proxy arch
                   -> MacawTHConfig arch opc t fs
                   -> MapF.MapF opc (ParameterizedFormula (Sym t fs) arch)
                   -- ^ A list of opcodes (with constraint information
                   -- witnessed) paired with the bytestrings containing their
                   -- semantics.  This comes from semmc.
                   -> [Some (DT.CaptureInfo opc)]
                   -- ^ Extra information for each opcode to let us generate
                   -- some TH to match them.  This comes from the semantics
                   -- definitions in semmc.
                   -> Library (Sym t fs)
                   -- ^ A list of defined function names paired with the
                   -- bytestrings containing their definitions.
                   -> U.LogCfg
                   -- ^ Logging configuration (explicit rather than
                   -- the typical implicit expression because I don't
                   -- know how to pass implicits to TH splices
                   -- invocations.
                   -> Q (Exp, [Dec])
genExecInstructionLogging _proxy thConf semantics captureInfo functions logcfg =
    U.withLogCfg logcfg $ do
      let lib = functions
      let formulas = semantics
      let formulasWithInfo = foldr (attachInfo formulas) MapF.empty captureInfo
      instructionMatcher thConf lib formulasWithInfo
        where
          attachInfo m0 (Some ci) m =
              let co = DT.capturedOpcode ci
              in case MapF.lookup co m0 of
                   Nothing -> m
                   Just pf -> MapF.insert co (Pair pf ci) m

natReprTH :: M.NatRepr w -> Q Exp
natReprTH w = [| knownNat :: M.NatRepr $(litT (numTyLit (intValue w))) |]

natReprFromIntTH :: Int -> Q Exp
natReprFromIntTH i = [| knownNat :: M.NatRepr $(litT (numTyLit (fromIntegral i))) |]

floatInfoTH :: M.FloatInfoRepr fi -> Q Exp
floatInfoTH fi = [| fi |]

floatInfoFromPrecisionTH :: CT.FloatPrecisionRepr fpp -> Q Exp
floatInfoFromPrecisionTH =
  floatInfoTH . M.floatInfoFromCrucible . SI.floatPrecisionToInfoRepr

-- | Sequence a list of monadic actions without constructing an intermediate
-- list structure
doSequenceQ :: [StmtQ] -> [Stmt] -> Q Exp
doSequenceQ stmts body = doE (stmts ++ map return body)

translateFormula :: forall arch opc t fs sh .
                    (A.Architecture arch)
                 => MacawTHConfig arch opc t fs
                 -> (String -> Maybe (MacawQ arch t fs Exp))
                 -> Name
                 -> ParameterizedFormula (Sym t fs) arch sh
                 -> BoundVarInterpretations arch t fs
                 -> SL.List (C.Const Name) sh
                 -> Q Exp
translateFormula thConf df ipVarName semantics interps varNames = do
  let preamble = [ bindS (varP (regsValName interps)) [| G.getRegs |] ]
  exps <- runMacawQ thConf df (mapM_ translateDefinition (MapF.toList (pfDefs semantics)))
  -- In the event that we have an empty list of expressions, insert a
  -- final return ()
  final <- NoBindS <$> [| return () |]
  let allExps = case exps of
        [] -> [final]
        _ -> exps
  [| Just $(doSequenceQ preamble allExps) |]
  where translateDefinition :: MapF.Pair (Parameter arch sh) (S.SymExpr (Sym t fs))
                            -> MacawQ arch t fs ()
        translateDefinition (MapF.Pair param expr) = do
          case param of
            OperandParameter _w idx -> do
              let C.Const name = varNames SL.!! idx
              newVal <- addEltTH (archEndianness thConf) interps expr
              appendStmt [| G.setRegVal (O.toRegister $(varE name)) =<< $(refBinding newVal) |]
            LiteralParameter loc
              -- FIXME: The below case is necessary for calls to
              -- defined functions that write to memory, but we end up
              -- calling locToRegTH on the memory object, which is a
              -- problem.
              -- -- | L.isMemoryLocation loc
              -- -- , S.NonceAppExpr n <- expr
              -- -- , S.FnApp symFn args <- S.nonceExprApp n
              -- -- , S.DefinedFnInfo {} <- S.symFnInfo symFn -> do
              -- --   let fnName = symFnName symFn
              -- --   funMaybe <- definedFunction fnName
              -- --   case funMaybe of
              -- --     Just fun -> do
              -- --       argExprs <- sequence $ FC.toListFC (addEltTH endianness interps) args
              -- --       return ()
              -- --       -- return $ foldl AppE fun argExprs
              -- --     Nothing -> fail ("Unknown defined function: " ++ fnName)
              | L.isMemoryLocation loc
              , S.NonceAppExpr n <- expr
              -> do
                  mtranslator <- withNonceAppEvaluator $ \evalNonceApp ->
                    return (evalNonceApp interps (S.nonceExprApp n))
                  case mtranslator of
                    Just translator -> do
                      _mem <- translator
                      appendStmt [| return () |]
                    _ | S.FnApp symFn args <- S.nonceExprApp n
                      , Just _ <- matchWriteMemWidth (symFnName symFn)
                      -> void $ writeMemTH interps symFn args (archEndianness thConf)
                    _ -> error "translateDefinition: unexpected memory write"

              -- -- | L.isMemoryLocation loc
              -- -- , S.BoundVarExpr bVar <- expr
              -- -- , Just loc <- MapF.lookup bVar (locVars interps) -> withLocToReg $ \ltr -> do
              -- --     return ()
              -- --     -- appendStmt [| error "BOUND VAR MEM" |]
              -- --     -- bindExpr expr [| return ($(varE (regsValName interps)) ^. M.boundValue $(ltr loc)) |]
              -- -- | L.isMemoryLocation loc
              -- -- , S.BoundVarExpr bVar <- expr -> do
              -- --     return ()
              -- --     -- , Nothing <- MapF.lookup bVar (locVars interps) -> withLocToReg $ \ltr -> do
              -- --     -- appendStmt [| error $(return $ LitE (StringL ("BAD BOUND VAR MEM: " <> show bVar))) |]
              -- -- | L.isMemoryLocation loc
              -- -- , S.AppExpr _ <- expr -> do
              -- --     error $ "WRITE TO MEM: APP"


              | otherwise -> do
                  valExp <- addEltTH (archEndianness thConf) interps expr
                  appendStmt [| G.setRegVal $(locationTranslator thConf loc) =<< $(refBinding valExp) |]
            FunctionParameter str (WrappedOperand _ opIx) _w -> do
              let C.Const boundOperandName = varNames SL.!! opIx
              case lookup str (A.locationFuncInterpretation (Proxy @arch)) of
                Nothing -> fail ("Function has no definition: " ++ str)
                Just fi -> do
                  valExp <- addEltTH (archEndianness thConf) interps expr
                  appendStmt [| case $(varE (A.exprInterpName fi)) $(varE boundOperandName) of
                                   Just reg -> G.setRegVal (O.toRegister reg) =<< $(refBinding valExp)
                                   Nothing -> fail ("Invalid instruction form at " ++ show $(varE ipVarName) ++ " in " ++ $(litE (stringL str)))
                               |]

translateFunction :: forall arch opc t fs args ret .
                     (A.Architecture arch)
                  => MacawTHConfig arch opc t fs
                  -> (String -> Maybe Name)
                  -- ^ names of all functions that we might call
                  -> (String -> Maybe (MacawQ arch t fs Exp))
                  -> FunctionFormula (Sym t fs) '(args, ret)
                  -> Q (Name, Dec, Dec)
translateFunction thConf fnName df ff = do
  let funNameErr = error ("Undefined function " ++ ffName ff)
  let var = fromMaybe funNameErr (fnName (ffName ff))
  argVars :: [Name]
    <- sequence $ FC.toListFC (\bv -> newName (bvarName bv)) (ffArgVars ff)
  let argVarMap :: MapF.MapF (SI.BoundVar (Sym t fs)) (C.Const Name)
      argVarMap = MapF.fromList $ zipWith pair bvs argVars
        where
          bvs :: [Some (SI.BoundVar (Sym t fs))]
          bvs = FC.toListFC Some (ffArgVars ff)
          pair (Some bv) v = Pair.Pair bv (C.Const v)
      interps = BoundVarInterpretations { locVars = MapF.empty
                                        , regsValName = mkName "<invalid>"
                                        -- only used for loc vars; we have none
                                        , opVars = MapF.empty
                                        , valVars = argVarMap }
      expr = case S.symFnInfo (ffDef ff) of
        S.DefinedFnInfo _ e _ -> e
        _ -> error $ "expected a defined function; found " ++ show (ffDef ff)
  stmts <- runMacawQ thConf df $ do
    val <- addEltTH (archEndianness thConf) interps expr
    appendStmt [| $(refBinding val) |]
  idsTy <- varT <$> newName "ids"
  sTy <- varT <$> newName "s"
  let translate :: forall tp. CT.BaseTypeRepr tp -> Q Type
      translate tp = case archTranslateType thConf idsTy sTy tp of
        Just t -> t
        Nothing -> [t| M.Value $(archTypeQ thConf) $(idsTy) $(translateBaseType tp) |]

      argHsTys = FC.toListFC translate (ffArgTypes ff)
      retHsTy = [t| G.Generator $(archTypeQ thConf) $(idsTy) $(sTy) $(translate (ffRetType ff)) |]
      ty = foldr (\a r -> [t| $(a) -> $(r) |]) retHsTy argHsTys
      body = doE (map return stmts)
  sig <- sigD var ty
  def <- funD var [clause (map varP argVars) (normalB body) []]
  return (var, sig, def)

translateBaseType :: CT.BaseTypeRepr tp -> Q Type
translateBaseType tp =  case tp of
  CT.BaseBoolRepr -> [t| M.BoolType |]
  CT.BaseBVRepr n -> appT [t| M.BVType |] (litT (numTyLit (intValue n)))
  _ -> fail $ "unsupported base type: " ++ show tp

translateBaseTypeRepr :: CT.BaseTypeRepr tp -> Q Exp
translateBaseTypeRepr tp =
  case tp of
    CT.BaseBoolRepr -> [| M.BoolTypeRepr |]
    CT.BaseBVRepr n -> [| M.BVTypeRepr $(natReprTH n) |]
    _ -> fail $ "unsupported base type: " ++ show tp

-- | wrapper around bitvector constants that forces some type
-- variables to match those of the monadic context.
bvValue :: 1 SI.<= w => NR.NatRepr w -> Integer -> M.Value arch ids (M.BVType w)
bvValue repr i = M.BVValue repr i

-- | Lift a bitvector value into a macaw float
genFloatValue
  :: ( MSS.SimplifierExtension arch
     , OrdF (M.ArchReg arch)
     , ShowF (M.ArchReg arch)
     , M.MemWidth (M.ArchAddrWidth arch)
     , 1 SI.<= w
     , (8 SI.* M.FloatInfoBytes ftp) ~ w
     )
  => NR.NatRepr w
  -> M.FloatInfoRepr ftp
  -> Integer
  -> G.Generator arch ids s (M.Value arch ids (M.FloatType ftp))
genFloatValue nr fi i = G.addExpr (G.AppExpr cast)
  where
    bv = M.BVValue nr i
    proof = M.ToFloat fi
    cast = M.Bitcast bv proof

addEltTH :: forall arch t fs ctp .
            (A.Architecture arch)
         => M.Endianness
         -> BoundVarInterpretations arch t fs
         -> S.Expr t ctp
         -> MacawQ arch t fs BoundExp
addEltTH endianness interps elt = do
  mexp <- lookupElt elt
  case mexp of
    Just e -> return e
    Nothing ->
      case elt of
        S.AppExpr appElt -> do
          -- AppExprs (general expression forms) can be translated either
          -- eagerly or lazily.  Eager translations use monadic bindings, while
          -- lazy bindings are let-bound expressions in the 'G.Generator' monad.
          --
          -- Note that the app translator will always return an Expr of
          -- 'G.Generator' type.  We will cache it here as a let binding.
          --
          -- NOTE: For now, we are translating all exprs of this form lazily.
          -- This may produce less dynamic sharing, but will be easier to manage
          -- for now.  Once that works, we can be smarter and translate what we
          -- can eagerly.
          (genExpr, ef) <- evalWithEffects $ appToExprTH endianness (S.appExprApp appElt) interps
          istl <- isTopLevel
          if istl || not ef
            then bindExpr elt (return genExpr)
            else letBindExpr elt genExpr
        S.BoundVarExpr bVar -> do
          x <- evalBoundVar interps bVar
          letBindPureExpr elt [| $(return x) |]
        S.NonceAppExpr n -> do
          (x, ef) <- evalWithEffects $ evalNonceAppTH endianness interps (S.nonceExprApp n)
          istl <- isTopLevel
          if istl || not ef
            then bindExpr elt (return x)
            else letBindExpr elt x
        S.SemiRingLiteral srTy val _
          | (SR.SemiRingBVRepr _ w) <- srTy ->
            -- Similar to the BoolExpr case, we always eagerly evaluate
            -- bitvector literals and return the VarE that wraps the name
            -- referring to the generated constant.
            letBindPureExpr elt [| bvValue $(natReprTH w) $(lift (BVS.asUnsigned val)) |]
          | otherwise -> EagerBoundExp <$> liftQ [| error "SemiRingLiteral Elts are not supported" |]
        S.FloatExpr prec flt _loc
          | Just Refl <- testEquality prec floatSingleRepr ->
            bindExpr elt [| genFloatValue $(natReprTH (knownNat @32)) M.SingleFloatRepr $(lift (BF.bfToBits (BF.float32 BF.NearEven) flt)) |]
          | Just Refl <- testEquality prec floatDoubleRepr ->
            bindExpr elt [| genFloatValue $(natReprTH (knownNat @64)) M.DoubleFloatRepr $(lift (BF.bfToBits (BF.float64 BF.NearEven) flt)) |]
          | otherwise ->
            EagerBoundExp <$> liftQ [| error "Unsupported float expression type" |]
        S.StringExpr {} -> EagerBoundExp <$> liftQ [| error "StringExpr elts are not supported" |]
        S.BoolExpr b _loc ->
          -- This case always eagerly evaluates the literal; that is fine.  It
          -- will be cached in the normal expression cache.  The value returned
          -- is the VarE that wraps the name referring to the generated
          -- constant.
          letBindPureExpr elt [| M.BoolValue $(lift b) |]



floatSingleRepr :: SI.FloatPrecisionRepr SI.Prec32
floatSingleRepr = knownRepr

floatDoubleRepr :: SI.FloatPrecisionRepr SI.Prec64
floatDoubleRepr = knownRepr

evalBoundVar :: forall arch t fs ctp .
                (A.Architecture arch)
             => BoundVarInterpretations arch t fs
             -> S.ExprBoundVar t ctp
             -> MacawQ arch t fs Exp
evalBoundVar interps bVar =
  if | Just loc <- MapF.lookup bVar (locVars interps) -> withLocToReg $ \ltr -> do
       liftQ [| ($(varE (regsValName interps)) ^. M.boundValue $(ltr loc)) |]
     | Just (C.Const name) <- MapF.lookup bVar (opVars interps) ->
       liftQ [| O.extractValue $(varE (regsValName interps)) $(varE name) |]
     | Just (C.Const name) <- MapF.lookup bVar (valVars interps) ->
       return (VarE name)
     | otherwise -> fail $ "bound var not found: " ++ show bVar

symFnName :: S.ExprSymFn t args ret -> String
symFnName = T.unpack . Sy.solverSymbolAsText . S.symFnName

bvarName :: S.ExprBoundVar t tp -> String
bvarName = T.unpack . Sy.solverSymbolAsText . S.bvarName

-- | Create Generator code to write a value to memory. We return the
-- argument that represents the memory in case it's needed.
writeMemTH :: forall arch t fs args ret
            . (A.Architecture arch)
           => BoundVarInterpretations arch t fs
           -> S.ExprSymFn t args ret
           -> Ctx.Assignment (S.Expr t) args
           -> M.Endianness
           -> MacawQ arch t fs (Some (S.Expr t))
writeMemTH bvi symFn args endianness =
  case FC.toListFC Some args of
    [Some mem, Some addr, Some val] -> case SI.exprType val of
      SI.BaseBVRepr memWidthRepr -> do
        -- FIXME: we aren't checking that the width is a multiple of 8.
        let memWidth = fromIntegral (intValue memWidthRepr) `div` 8
        addrValExp <- addEltTH endianness bvi addr
        writtenValExp <- addEltTH endianness bvi val
        appendStmt [| G.addStmt =<< (M.WriteMem <$> $(refBinding addrValExp) <*> pure (M.BVMemRepr $(natReprFromIntTH memWidth) endianness) <*> $(refBinding writtenValExp)) |]
        return (Some mem)
      tp -> fail ("Invalid memory write value type for " <> symFnName symFn <> ": " <> showF tp)
    l -> fail ("Invalid memory write argument list for " <> symFnName symFn <> ": " <> show l)

-- FIXME: Generalize this to take a symFn, checking the name, argument
-- types, and return type (possibly)
-- | Match a "write_mem" intrinsic and return the number of bytes written
matchWriteMemWidth :: String -> Maybe Int
matchWriteMemWidth s = do
  suffix <- L.stripPrefix "uf_write_mem_" s
  (`div` 8) <$> readMaybe suffix

evalNonceAppTH :: forall arch t fs tp
                . (A.Architecture arch)
               => M.Endianness
               -> BoundVarInterpretations arch t fs
               -> S.NonceApp t (S.Expr t) tp
               -> MacawQ arch t fs Exp
evalNonceAppTH endianness bvi nonceApp = do
  mtranslator <- withNonceAppEvaluator $ \evalNonceApp -> return (evalNonceApp bvi nonceApp)
  case mtranslator of
    Just translator -> translator
    Nothing -> defaultNonceAppEvaluator endianness bvi nonceApp

addApp :: ( MSS.SimplifierExtension arch
          , OrdF (M.ArchReg arch)
          , M.MemWidth (M.RegAddrWidth (M.ArchReg arch))
          , ShowF (M.ArchReg arch)
          )
       => M.App (M.Value arch ids) tp
       -> G.Generator arch ids s (M.Value arch ids tp)
addApp a = G.addExpr (G.AppExpr a)

defaultNonceAppEvaluator :: forall arch t fs tp
                          . (A.Architecture arch)
                         => M.Endianness
                         -> BoundVarInterpretations arch t fs
                         -> S.NonceApp t (S.Expr t) tp
                         -> MacawQ arch t fs Exp
defaultNonceAppEvaluator endianness bvi nonceApp =
  case nonceApp of
    S.FnApp symFn args -> do
      let fnName = symFnName symFn
      funMaybe <- definedFunction fnName
      case funMaybe of
        Just fun -> do
          argExprs <- sequence $ FC.toListFC (addEltTH endianness bvi) args
          setEffectful
          case all isEager argExprs of
            True -> liftQ $ foldl appE (return fun) (map refEager argExprs)
            False -> do
              let applyQ e be = [| $(e) `ap` $(refBinding be) |]
              liftQ [| join $(foldl applyQ [| return $(return fun) |] argExprs) |]
        _ -> do
          let fnArgTypes = S.symFnArgTypes symFn
              fnRetType = S.symFnReturnType symFn
          case fnName of
            -- For count leading zeros, we don't have a SimpleBuilder term to reduce
            -- it to, so we have to manually transform it to macaw here (i.e., we
            -- can't use the more general substitution method, since that is in
            -- terms of rewriting simplebuilder).
            "uf_clz_32" ->
              case FC.toListFC Some args of
                [Some loc] -> do
                  locExp <- addEltTH endianness bvi loc
                  liftQ [| addApp =<< (M.Bsr (NR.knownNat @32) <$> $(refBinding locExp)) |]
                _ -> fail ("Unsupported argument list for clz: " ++ showF args)
            "uf_clz_64" ->
              case FC.toListFC Some args of
                [Some loc] -> do
                  locExp <- addEltTH endianness bvi loc
                  liftQ [| addApp =<< (M.Bsr (NR.knownNat @64) <$> $(refBinding locExp)) |]
                _ -> fail ("Unsupported argument list for clz: " ++ showF args)
            "uf_popcnt_32" ->
              case FC.toListFC Some args of
                [Some loc] -> do
                  locExp <- addEltTH endianness bvi loc
                  liftQ [| addApp =<< (M.PopCount (NR.knownNat @32) <$> $(refBinding locExp)) |]
                _ -> fail ("Unsupported argument list for popcnt: " ++ showF args)
            "uf_popcnt_64" ->
              case FC.toListFC Some args of
                [Some loc] -> do
                  locExp <- addEltTH endianness bvi loc
                  liftQ [| addApp =<< (M.PopCount (NR.knownNat @64) <$> $(refBinding locExp)) |]
                _ -> fail ("Unsupported argument list for popcnt: " ++ showF args)
            "uf_undefined" -> do
              case S.nonceAppType nonceApp of
                CT.BaseBVRepr n ->
                  liftQ [| M.AssignedValue <$> G.addAssignment (M.SetUndefined (M.BVTypeRepr $(natReprTH n))) |]
                nt -> fail ("Invalid type for undefined: " ++ show nt)
            _ | Just nBytes <- readMemBytes fnName -> do
                case FC.toListFC Some args of
                  [_, Some addrElt] -> do
                    -- read_mem has a shape such that we expect two arguments; the
                    -- first is just a stand-in in the semantics to represent the
                    -- memory.
                    addr <- addEltTH endianness bvi addrElt
                    setEffectful
                    liftQ [| let memRep = M.BVMemRepr (NR.knownNat :: NR.NatRepr $(litT (numTyLit (fromIntegral nBytes)))) endianness
                                 assignGen = join (G.addAssignment <$> (M.ReadMem <$> $(refBinding addr) <*> pure memRep))
                              in M.AssignedValue <$> assignGen
                           |]
                  _ -> fail ("Unexpected arguments to read_mem: " ++ showF args)
              | let interp = A.locationFuncInterpretation (Proxy @arch)
              , Just fi <- lookup fnName interp -> do
                  -- args is an assignment that contains elts; we could just generate
                  -- expressions that evaluate each one and then splat them into new names
                  -- that we apply our name to.
                  case FC.toListFC (asName fnName bvi) args of
                    [] -> fail ("zero-argument uninterpreted functions are not supported: " ++ fnName)
                    argNames -> do
                      let call = appE (varE (A.exprInterpName fi)) $ foldr1 appE (map varE argNames)
                      liftQ [| return $ O.extractValue $(varE (regsValName bvi)) ($(call)) |]
              | Just _ <- matchWriteMemWidth fnName -> do
                Some memExpr <- writeMemTH bvi symFn args endianness
                mem <- addEltTH endianness bvi memExpr
                setEffectful
                liftQ [| return $(refBinding mem) |]
              | otherwise -> error $ "Unsupported function: " ++ show fnName ++ "(" ++ show fnArgTypes ++ ") -> " ++ show fnRetType
    _ -> error "Unsupported NonceApp case"

-- | Parse the name of a memory read intrinsic and return the number of bytes
-- that it reads.  For example
--
-- > readMemBytes "read_mem_8" == Just 1
readMemBytes :: String -> Maybe Int
readMemBytes s = do
  nBitsStr <- L.stripPrefix "uf_read_mem_" s
  nBits <- readMaybe nBitsStr
  return (nBits `div` 8)

asName :: String -> BoundVarInterpretations arch t fs -> S.Expr t tp -> Name
asName ufName bvInterps elt =
  case elt of
    S.BoundVarExpr bVar ->
      case MapF.lookup bVar (opVars bvInterps) of
        Nothing -> error ("Expected " ++ show bVar ++ " to have an interpretation")
        Just (C.Const name) -> name
    _ -> error ("Unexpected elt as name (" ++ showF elt ++ ") in " ++ ufName)

appToExprTH :: (A.Architecture arch)
            => M.Endianness
            -> S.App (S.Expr t) tp
            -> BoundVarInterpretations arch t fs
            -> MacawQ arch t fs Exp
appToExprTH endianness app interps = do
  mtranslator <- withAppEvaluator $ \evalApp -> return (evalApp interps app)
  case mtranslator of
    Just translator -> translator
    Nothing -> defaultAppEvaluator endianness app interps

defaultAppEvaluator :: (A.Architecture arch)
                    => M.Endianness
                    -> S.App (S.Expr t) ctp
                    -> BoundVarInterpretations arch t fs
                    -> MacawQ arch t fs Exp
defaultAppEvaluator endianness elt interps = case elt of
  S.NotPred bool -> do
    e <- addEltTH endianness interps bool
    liftQ $ joinPure1 [| addApp |] [| M.NotApp |] e
  S.ConjPred conj -> do
    l <- conjList (addEltTH endianness interps) conj
    case all (\(bnd,_) -> isEager bnd) l of
      True -> do
        tms <- liftQ $ listE $ map (\(bnd, b) -> (tupE [refEager bnd, lift b])) l
        liftQ [| allPreds $(return tms) |]
      False -> do
        tms <- liftQ $ listE $ map (\(bnd, b) -> (tupE [refBinding bnd, lift b])) l
        liftQ [| joinPreds $(return tms) |]
  S.BaseIte bt _ test t f -> do
    -- FIXME: Generate code that dynamically checks for a concrete condition and
    -- make an ite instead of a mux if possible

    testE <- addEltTH endianness interps test
    tE <- addEltTH endianness interps t
    fE <- addEltTH endianness interps f
    case bt of
      CT.BaseBoolRepr -> liftQ $ joinPure3 [| addApp |] [| M.Mux M.BoolTypeRepr |] testE tE fE
      CT.BaseBVRepr w -> liftQ $ joinPure3 [| addApp |] [| M.Mux (M.BVTypeRepr $(natReprTH w)) |] testE tE fE
      CT.BaseFloatRepr fpp -> liftQ $ joinPure3 [| addApp |] [| M.Mux (M.FloatTypeRepr $(floatInfoFromPrecisionTH fpp)) |] testE tE fE
      CT.BaseIntegerRepr -> liftQ [| error "Macaw semantics for integer ITE unsupported" |]
      CT.BaseRealRepr -> liftQ [| error "Macaw semantics for real ITE unsupported" |]
      CT.BaseStringRepr {} -> liftQ [| error "Macaw semantics for string ITE unsupported" |]
      CT.BaseComplexRepr -> liftQ [| error "Macaw semantics for complex ITE unsupported" |]
      CT.BaseStructRepr {} -> liftQ [| error "Macaw semantics for struct ITE unsupported" |]
      CT.BaseArrayRepr {} -> liftQ [| error "Macaw semantics for array ITE unsupported" |]

  S.BaseEq _bt bv1 bv2 -> do
    e1 <- addEltTH endianness interps bv1
    e2 <- addEltTH endianness interps bv2
    liftQ $ joinPure2 [| addApp |] [| M.Eq |] e1 e2
  S.BVSlt bv1 bv2 -> do
    e1 <- addEltTH endianness interps bv1
    e2 <- addEltTH endianness interps bv2
    liftQ $ joinPure2 [| addApp |] [| M.BVSignedLt |] e1 e2
  S.BVUlt bv1 bv2 -> do
    e1 <- addEltTH endianness interps bv1
    e2 <- addEltTH endianness interps bv2
    liftQ $ joinPure2 [| addApp |] [| M.BVUnsignedLt |] e1 e2
  S.BVConcat w bv1 bv2 -> do
    let u = S.bvWidth bv1
        v = S.bvWidth bv2
    e1 <- addEltTH endianness interps bv1
    e2 <- addEltTH endianness interps bv2
    liftQ $ [| G.addExpr =<< $(joinOp2 [| \v1 v2 -> TR.bvconcat v1 v2 $(natReprTH v) $(natReprTH u) $(natReprTH w) |] e1 e2) |]
  S.BVSelect idx n bv -> do
    let w = S.bvWidth bv
    case natValue n + 1 <= natValue w of
      True -> do
        e <- addEltTH endianness interps bv
        liftQ [| G.addExpr =<< $(joinOp1 [| \v1 -> TR.bvselect v1 $(natReprTH n) $(natReprTH idx) $(natReprTH w) |] e) |]
      False -> do
        e <- addEltTH endianness interps bv
        liftQ [| case testEquality $(natReprTH n) $(natReprTH w) of
                   Just Refl -> return $(refBinding e)
                   Nothing -> error "Invalid reprs for BVSelect translation"
               |]
  S.BVTestBit idx bv -> do
    bvValExp <- addEltTH endianness interps bv
    liftQ $ joinPure1 [| addApp |] [| M.BVTestBit (M.BVValue $(natReprTH (S.bvWidth bv)) $(lift (toInteger idx))) |] bvValExp

  S.SemiRingSum sm ->
    case WSum.sumRepr sm of
      SR.SemiRingBVRepr fl w ->
        let smul mul e = do
              y <- addEltTH endianness interps e
              return $ [(y, BVS.asUnsigned mul)]
            one = case fl of
              SR.BVArithRepr -> 1
              SR.BVBitsRepr -> SI.maxUnsigned w
            sval v = do
              bnd <- EagerBoundExp <$> liftQ [| M.BVValue $(natReprTH w) $(lift (BVS.asUnsigned v)) |]
              return $ [(bnd, one)]

        in do
          bnds <- WSum.evalM (\a b -> return $ a ++ b) smul sval sm
          case all (\(bnd,_) -> isEager bnd) bnds of
            True -> do
              tms <- liftQ $ listE $ map (\(bnd, i) -> (tupE [refEager bnd, lift i])) bnds
              liftQ [| sumBVs $(liftFlavor fl) $(natReprTH w) $(return tms) |]
            False -> do
              tms <- liftQ $ listE $ map (\(bnd, i) -> (tupE [refBinding bnd, lift i])) bnds
              liftQ [| joinSumBVs $(liftFlavor fl) $(natReprTH w) $(return tms) |]
      _ -> liftQ [| error "unsupported SemiRingSum repr for macaw semmc TH" |]

  S.SemiRingProd pd ->
    case WSum.prodRepr pd of
      SR.SemiRingBVRepr SR.BVArithRepr w ->
        let pmul x y = do
              bindPure2 [| addApp |] [| M.BVMul $(natReprTH w) |] x y
            unit = liftQ [| pure (M.BVValue $(natReprTH w) 1) |]
            convert = addEltTH endianness interps
        in WSum.prodEvalM pmul convert pd >>= maybe unit extractBound
      SR.SemiRingBVRepr SR.BVBitsRepr w ->
        let pmul x y = do
              bindPure2 [| addApp |] [| M.BVAnd $(natReprTH w) |] x y
            unit = liftQ [| pure (M.BVValue $(natReprTH w) $(lift $ SI.maxUnsigned w)) |]
            convert = addEltTH endianness interps
        in WSum.prodEvalM pmul convert pd >>= maybe unit extractBound
      _ -> liftQ [| error "unsupported SemiRingProd repr for macaw semmc TH" |]

  S.BVOrBits w bs -> do
    -- This is a TH Expr that is of type (Macaw) Value at run-time
    zero <- liftQ [| (M.BVValue $(natReprTH w) 0) |]
    -- These are all TH Exprs that are of the (Macaw) Value at run-time
    bs' <- mapM (addEltTH endianness interps) (S.bvOrToList bs)
    let por x y = do
          bindPure2 [| addApp |] [| M.BVOr $(natReprTH w) |] x y
    F.foldrM por (EagerBoundExp zero) bs' >>= extractBound

  S.BVShl w bv1 bv2 -> do
    e1 <- addEltTH endianness interps bv1
    e2 <- addEltTH endianness interps bv2
    liftQ $ joinPure2 [| addApp |] [| M.BVShl $(natReprTH w) |] e1 e2
  S.BVLshr w bv1 bv2 -> do
    e1 <- addEltTH endianness interps bv1
    e2 <- addEltTH endianness interps bv2
    liftQ $ joinPure2 [| addApp |] [| M.BVShr $(natReprTH w) |] e1 e2
  S.BVAshr w bv1 bv2 -> do
    e1 <- addEltTH endianness interps bv1
    e2 <- addEltTH endianness interps bv2
    liftQ $ joinPure2 [| addApp |] [| M.BVSar $(natReprTH w) |] e1 e2
  S.BVZext w bv -> do
    e <- addEltTH endianness interps bv
    liftQ $ joinPure1 [| addApp |] [| (\x -> M.UExt x $(natReprTH w)) |] e
  S.BVSext w bv -> do
    e <- addEltTH endianness interps bv
    liftQ $ joinPure1 [| addApp |] [| (\x -> M.SExt x $(natReprTH w)) |] e

  _ -> error $ "unsupported Crucible elt: " <> show elt

----------------------------------------------------------------------

getBVOps ::  1 SI.<= n
         => CT.NatRepr n
         -> SR.BVFlavorRepr t
         -> (M.Value arch ids (M.BVType n)
              -> M.Value arch ids (M.BVType n)
              -> M.App (M.Value arch ids) (M.BVType n)
            , M.Value arch ids (M.BVType n)
              -> M.Value arch ids (M.BVType n)
              -> M.App (M.Value arch ids) (M.BVType n))
getBVOps repr fl = case fl of
    SR.BVArithRepr -> (M.BVMul repr, M.BVAdd repr)
    SR.BVBitsRepr -> (M.BVAnd repr, M.BVXor repr)

liftFlavor :: SR.BVFlavorRepr t -> Q Exp
liftFlavor fl = case fl of
  SR.BVArithRepr -> [| SR.BVArithRepr |]
  SR.BVBitsRepr -> [| SR.BVBitsRepr |]

sumBVs :: 1 SI.<= n
       => ( MSS.SimplifierExtension arch
          , OrdF (M.ArchReg arch)
          , M.MemWidth (M.RegAddrWidth (M.ArchReg arch))
          , ShowF (M.ArchReg arch)
          )
       => SR.BVFlavorRepr t
       -> CT.NatRepr n
       -> [(M.Value arch ids (M.BVType n), Integer)]
       -> G.Generator arch ids s (M.Value arch ids (M.BVType n))
sumBVs fl repr vs = do
  let (mulOp, addOp) = getBVOps repr fl
  vals <- mapM (\(x,y) -> G.addExpr $ G.AppExpr $ mulOp x (M.BVValue repr y)) vs
  foldM (\a b -> G.addExpr $ G.AppExpr $ addOp a b) (M.BVValue repr 0) vals

joinSumBVs :: 1 SI.<= n
           => ( MSS.SimplifierExtension arch
              , OrdF (M.ArchReg arch)
              , M.MemWidth (M.RegAddrWidth (M.ArchReg arch))
              , ShowF (M.ArchReg arch)
              )
           => SR.BVFlavorRepr t
           -> CT.NatRepr n
           -> [(G.Generator arch ids s (M.Value arch ids (M.BVType n)), Integer)]
           -> G.Generator arch ids s (M.Value arch ids (M.BVType n))
joinSumBVs fl repr vs = do
  let (mulOp, addOp) = getBVOps repr fl
  vals <- mapM (\(xF,y) -> xF >>= \x -> G.addExpr $ G.AppExpr $ mulOp x (M.BVValue repr y)) vs
  foldM (\a b -> G.addExpr $ G.AppExpr $ addOp a b) (M.BVValue repr 0) vals


allPreds :: ( MSS.SimplifierExtension arch
            , OrdF (M.ArchReg arch)
            , M.MemWidth (M.RegAddrWidth (M.ArchReg arch))
            , ShowF (M.ArchReg arch)
            )
         => [(M.Value arch ids M.BoolType, Bool)]
         -> G.Generator arch ids s (M.Value arch ids M.BoolType)
allPreds vs = do
  let
    mkApp b (a, True) =  G.addExpr $ G.AppExpr $ M.AndApp a b
    mkApp b (a, False) = do
      notA <- G.addExpr $ G.AppExpr $ M.NotApp a
      G.addExpr $ G.AppExpr $ M.AndApp notA b
  foldM mkApp (M.BoolValue True) vs

joinPreds :: ( MSS.SimplifierExtension arch
             , OrdF (M.ArchReg arch)
             , M.MemWidth (M.RegAddrWidth (M.ArchReg arch))
             , ShowF (M.ArchReg arch)
             )
          => [(G.Generator arch ids s (M.Value arch ids M.BoolType), Bool)]
          -> G.Generator arch ids s (M.Value arch ids M.BoolType)
joinPreds vs = do
  let
    mkApp b (aF, True) = do
      a <- aF
      G.addExpr $ G.AppExpr $ M.AndApp a b
    mkApp b (aF, False) = do
      a <- aF
      notA <- G.addExpr $ G.AppExpr $ M.NotApp a
      G.addExpr $ G.AppExpr $ M.AndApp notA b
  foldM mkApp (M.BoolValue True) vs



conjList :: (forall tp. S.Expr t tp -> MacawQ arch t fs BoundExp)
            -> BooM.ConjMap (S.Expr t)
            -> MacawQ arch t fs [(BoundExp, Bool)]
conjList f bm = case BooM.viewConjMap bm of
  BooM.ConjTrue -> return []
  BooM.ConjFalse -> do
    bnd <- EagerBoundExp <$> liftQ [| M.BoolValue False |]
    return $ [(bnd, True)]
  BooM.Conjuncts ts -> liftM NE.toList $ forM ts $ \(e, p) -> do
    eE <- f e
    return $ (eE, p == BooM.Positive)

conPCompat :: Name -> [Pat] -> Pat
conPCompat n pats = ConP n
#if MIN_VERSION_template_haskell(2,18,0)
                           []
#endif
                           pats
