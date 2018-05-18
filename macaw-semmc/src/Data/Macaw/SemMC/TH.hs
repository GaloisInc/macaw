{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
-- | Architecture-independent translation of semmc semantics (via SimpleBuilder)
-- into macaw IR.
--
-- The main entry point is 'genExecInstruction', which is customized for
-- architecture-specific backends via some parameters.
--
-- The other functions exposed by this module are useful for implementing
-- architecture-specific translations.

module Data.Macaw.SemMC.TH (
  genExecInstruction,
  genExecInstructionLogStdErr,
  genExecInstructionLogging,
  addEltTH,
  natReprTH,
  symFnName,
  asName
  ) where

import           GHC.TypeLits ( Symbol )
import qualified Data.ByteString as BS

import           Control.Lens ( (^.) )
import qualified Control.Concurrent.Async as Async
import qualified Data.Functor.Const as C
import           Data.Proxy ( Proxy(..) )
import qualified Data.List as L
import           Data.Semigroup
import qualified Data.Text as T
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import           Text.Read ( readMaybe )

import           Data.Parameterized.Classes
import qualified Data.Parameterized.HasRepr as HR
import qualified Data.Parameterized.Lift as LF
import qualified Data.Parameterized.List as SL
import qualified Data.Parameterized.Map as Map
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Lang.Crucible.Backend.Simple as S
import qualified What4.BaseTypes as CT
import qualified What4.Expr.Builder as S
import qualified What4.Interface as SI
import qualified What4.Symbol as Sy

import qualified Dismantle.Instruction as D
import qualified Dismantle.Tablegen.TH.Capture as DT

import qualified SemMC.BoundVar as BV
import           SemMC.Formula
import qualified SemMC.Architecture as A
import qualified SemMC.Architecture.Location as L
import qualified SemMC.Util as U
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Types as M

import Data.Parameterized.NatRepr ( knownNat
                                  , natValue
                                  )

import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Operands as O
import qualified Data.Macaw.SemMC.Translations as TR
import           Data.Macaw.SemMC.TH.Monad

type Sym t = S.SimpleBackend t

-- | A different parameterized pair wrapper; the one in Data.Parameterized.Map
-- hides the @tp@ parameter under an existential, while we need the variant that
-- exposes it.
data PairF a b tp = PairF (a tp) (b tp)

-- | Generate the top-level lambda with a case expression over an instruction
-- (casing on opcode)
--
-- > \ipVar (Instruction opcode operandList) ->
-- >   case opcode of
-- >     ${CASES}
--
-- where each case in ${CASES} is defined by 'mkSemanticsCase'; each case
-- matches one opcode.
instructionMatcher :: (OrdF a, LF.LiftF a, A.Architecture arch)
                   => (forall tp . L.Location arch tp -> Q Exp)
                   -> (forall tp . BoundVarInterpretations arch t -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                   -> (forall tp . BoundVarInterpretations arch t -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                   -> Name
                   -- ^ The name of the architecture-specific instruction
                   -- matcher to run before falling back to the generic one
                   -> Map.MapF a (PairF (ParameterizedFormula (Sym t) arch) (DT.CaptureInfo a))
                   -> (Q Type, Q Type)
                   -> Q Exp
instructionMatcher ltr ena ae archSpecificMatcher formulas operandResultType = do
  ipVarName <- newName "ipVal"
  opcodeVar <- newName "opcode"
  operandListVar <- newName "operands"
  (normalCases, bodyDefs) <- unzip <$> mapM (mkSemanticsCase ltr ena ae ipVarName operandListVar operandResultType) (Map.toList formulas)
  (fallthruNm, unimp) <- unimplementedInstruction
  fallthroughCase <- match wildP (normalB (appE (varE fallthruNm) (varE opcodeVar))) []
  let allCases :: [Match]
      allCases = concat [ normalCases
                        , [fallthroughCase]
                        ]
  instrVar <- newName "i"
  instrArg <- asP instrVar [p| D.Instruction $(varP opcodeVar) $(varP operandListVar) |]
  matcherRes <- appE (varE archSpecificMatcher) (varE instrVar)
  actionVar <- newName "action"
  let instrCase = LetE (unimp : fullDefs) $ CaseE (VarE opcodeVar) allCases
      fullDefs = concatMap (\(t,i) -> [t,i]) bodyDefs
  return $ LamE [(VarP ipVarName), instrArg] $
         CaseE matcherRes
                   [ Match (ConP 'Just [VarP actionVar])
                               (NormalB $ AppE (ConE 'Just) (VarE actionVar)) []
                   , Match (ConP 'Nothing [])
                               (NormalB instrCase) []
                   ]


unimplementedInstruction :: Q (Name, Dec)
unimplementedInstruction = do
    fname <- newName "noMatch"
    arg1Nm <- newName "unknownOpcode"
    fdecl <- funD fname
             [clause [varP arg1Nm]
                         (normalB [| error ("Unimplemented instruction: " ++ show $(varE arg1Nm)) |])
                         []]
    return (fname, fdecl)


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
mkSemanticsCase :: (LF.LiftF a, A.Architecture arch)
                => (forall tp . L.Location arch tp -> Q Exp)
                -> (forall tp . BoundVarInterpretations arch t -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                -> (forall tp . BoundVarInterpretations arch t -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                -> Name
                -> Name
                -> (Q Type, Q Type)
                -> Map.Pair a (PairF (ParameterizedFormula (Sym t) arch) (DT.CaptureInfo a))
                -> Q (Match, (Dec, Dec))
mkSemanticsCase ltr ena ae ipVarName operandListVar operandResultType (Map.Pair opc (PairF semantics capInfo)) =
    do arg1Nm <- newName "operands"
       ofname <- newName $ "opc_" <> (filter ((/=) '"') $ nameBase $ DT.capturedOpcodeName capInfo)
       lTypeVar <- newName "l"
       idsTypeVar <- newName "ids"
       sTypeVar <- newName "s"
       ofsig <- sigD ofname [t| SL.List $(fst operandResultType) $(varT lTypeVar)
                                  -> Maybe (G.Generator $(snd operandResultType)
                                                        $(varT idsTypeVar)
                                                        $(varT sTypeVar) ()) |]
       ofdef <- funD ofname
                 [clause [varP arg1Nm]
                  (normalB (mkOperandListCase ltr ena ae ipVarName arg1Nm opc semantics capInfo))
                  []]
       mtch <- match (conP (DT.capturedOpcodeName capInfo) []) (normalB (appE (varE ofname) (varE operandListVar))) []
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
                  => (forall tp0 . L.Location arch tp0 -> Q Exp)
                  -> (forall tp0 . BoundVarInterpretations arch t -> S.NonceApp t (S.Expr t) tp0 -> Maybe (MacawQ arch t Exp))
                  -> (forall tp0 . BoundVarInterpretations arch t -> S.App (S.Expr t) tp0 -> Maybe (MacawQ arch t Exp))
                  -> Name
                  -> Name
                  -> a tp
                  -> ParameterizedFormula (Sym t) arch tp
                  -> DT.CaptureInfo a tp
                  -> Q Exp
mkOperandListCase ltr ena ae ipVarName operandListVar opc semantics capInfo = do
  body <- genCaseBody ltr ena ae ipVarName opc semantics (DT.capturedOperandNames capInfo)
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
genCaseBody :: forall a sh t arch
             . (A.Architecture arch)
            => (forall tp . L.Location arch tp -> Q Exp)
            -> (forall tp . BoundVarInterpretations arch t -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
            -> (forall tp . BoundVarInterpretations arch t -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
            -> Name
            -> a sh
            -> ParameterizedFormula (Sym t) arch sh
            -> SL.List (C.Const Name) sh
            -> Q Exp
genCaseBody ltr ena ae ipVarName _opc semantics varNames = do
  regsName <- newName "_regs"
  translateFormula ltr ena ae ipVarName semantics (BoundVarInterpretations locVarsMap opVarsMap regsName) varNames
  where
    locVarsMap :: Map.MapF (SI.BoundVar (Sym t)) (L.Location arch)
    locVarsMap = Map.foldrWithKey (collectVarForLocation (Proxy @arch)) Map.empty (pfLiteralVars semantics)

    opVarsMap :: Map.MapF (SI.BoundVar (Sym t)) (C.Const Name)
    opVarsMap = SL.ifoldr (collectOperandVars varNames) Map.empty (pfOperandVars semantics)

collectVarForLocation :: forall tp arch proxy t
                       . proxy arch
                      -> L.Location arch tp
                      -> SI.BoundVar (Sym t) tp
                      -> Map.MapF (SI.BoundVar (Sym t)) (L.Location arch)
                      -> Map.MapF (SI.BoundVar (Sym t)) (L.Location arch)
collectVarForLocation _ loc bv = Map.insert bv loc

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
collectOperandVars :: forall sh tp arch t
                    . SL.List (C.Const Name) sh
                   -> SL.Index sh tp
                   -> BV.BoundVar (Sym t) arch tp
                   -> Map.MapF (SI.BoundVar (Sym t)) (C.Const Name)
                   -> Map.MapF (SI.BoundVar (Sym t)) (C.Const Name)
collectOperandVars varNames ix (BV.BoundVar bv) m =
  case varNames SL.!! ix of
    C.Const name -> Map.insert bv (C.Const name) m
{-
     genExecInstruction :: forall k arch (a :: [k] -> *) (proxy :: *
                                                                        -> *).
                                (A.Architecture arch, OrdF a, ShowF a, LF.LiftF a) =>
                                proxy arch
                                -> (forall (tp :: CT.BaseType). L.Location arch tp -> Q Exp)
                                -> (forall (tp :: CT.BaseType) t.

-}
-- | Wrapper for 'genExecInstructionLogging' which generates a no-op
-- LogCfg to disable any logging during the generation.
genExecInstruction :: forall arch (a :: [Symbol] -> *) (proxy :: * -> *)
                    . (A.Architecture arch,
                       HR.HasRepr a (A.ShapeRepr arch),
                       OrdF a,
                       ShowF a,
                       LF.LiftF a)
                   => proxy arch
                   -> (forall tp . L.Location arch tp -> Q Exp)
                   -- ^ A translation of 'L.Location' references into 'Exp's
                   -- that generate macaw IR to reference those expressions
                   -> (forall tp t . BoundVarInterpretations arch t -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                   -- ^ A translation of uninterpreted functions into macaw IR;
                   -- returns 'Nothing' if the handler does not know how to
                   -- translate the 'S.NonceApp'.
                   -> (forall tp t . BoundVarInterpretations arch t -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                   -- ^ Similarly, a translator for 'S.App's; mostly intended to
                   -- translate division operations into architecture-specific
                   -- statements, which have no representation in macaw.
                   -> Name
                   -- ^ The arch-specific instruction matcher for translating
                   -- instructions directly into macaw IR; this is usually used
                   -- for translating trap and system call type instructions.
                   -- This has to be specified by 'Name' instead of as a normal
                   -- function, as the type would actually refer to types that
                   -- we cannot mention in this shared code (i.e.,
                   -- architecture-specific instruction types).
                   -> [(Some a, BS.ByteString)]
                   -- ^ A list of opcodes (with constraint information
                   -- witnessed) paired with the bytestrings containing their
                   -- semantics.  This comes from semmc.
                   -> [Some (DT.CaptureInfo a)]
                   -- ^ Extra information for each opcode to let us generate
                   -- some TH to match them.  This comes from the semantics
                   -- definitions in semmc.
                   -> (Q Type, Q Type)
                   -> Q Exp
genExecInstruction _ ltr ena ae archInsnMatcher semantics captureInfo operandResultType = do
  logCfg <- runIO $ U.mkNonLogCfg
  r <- genExecInstructionLogging (Proxy @arch) ltr ena ae archInsnMatcher semantics captureInfo operandResultType logCfg
  runIO $ U.logEndWith logCfg
  return r

-- | Wrapper for 'genExecInstructionLogging' which generates a no-op
-- LogCfg to disable any logging during the generation.
genExecInstructionLogStdErr :: forall arch (a :: [Symbol] -> *) (proxy :: * -> *)
                    . (A.Architecture arch,
                       HR.HasRepr a (A.ShapeRepr arch),
                       OrdF a,
                       ShowF a,
                       LF.LiftF a)
                   => proxy arch
                   -> (forall tp . L.Location arch tp -> Q Exp)
                   -- ^ A translation of 'L.Location' references into 'Exp's
                   -- that generate macaw IR to reference those expressions
                   -> (forall tp t . BoundVarInterpretations arch t -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                   -- ^ A translation of uninterpreted functions into macaw IR;
                   -- returns 'Nothing' if the handler does not know how to
                   -- translate the 'S.NonceApp'.
                   -> (forall tp t . BoundVarInterpretations arch t -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                   -- ^ Similarly, a translator for 'S.App's; mostly intended to
                   -- translate division operations into architecture-specific
                   -- statements, which have no representation in macaw.
                   -> Name
                   -- ^ The arch-specific instruction matcher for translating
                   -- instructions directly into macaw IR; this is usually used
                   -- for translating trap and system call type instructions.
                   -- This has to be specified by 'Name' instead of as a normal
                   -- function, as the type would actually refer to types that
                   -- we cannot mention in this shared code (i.e.,
                   -- architecture-specific instruction types).
                   -> [(Some a, BS.ByteString)]
                   -- ^ A list of opcodes (with constraint information
                   -- witnessed) paired with the bytestrings containing their
                   -- semantics.  This comes from semmc.
                   -> [Some (DT.CaptureInfo a)]
                   -- ^ Extra information for each opcode to let us generate
                   -- some TH to match them.  This comes from the semantics
                   -- definitions in semmc.
                   -> (Q Type, Q Type)
                   -> Q Exp
genExecInstructionLogStdErr _ ltr ena ae archInsnMatcher semantics captureInfo operandResultType = do
  logCfg <- runIO $ U.mkLogCfg "genExecInstruction"
  logThread <- runIO $ U.asyncLinked (U.stdErrLogEventConsumer (const True) logCfg)
  r <- genExecInstructionLogging (Proxy @arch) ltr ena ae archInsnMatcher semantics captureInfo operandResultType logCfg
  runIO $ U.logEndWith logCfg
  runIO $ Async.wait logThread
  return r

-- | Generate an implementation of 'execInstruction' that runs in the
-- 'G.Generator' monad.  We pass in both the original list of semantics files
-- along with the list of opcode info objects.  We can match them up using
-- equality on opcodes (via a MapF).  Generating a combined list up-front would
-- be ideal, but is difficult for various TH reasons (we can't call 'lift' on
-- all of the things we would need to for that).
--
-- The structure of the term produced is documented in 'instructionMatcher'
genExecInstructionLogging :: forall arch (a :: [Symbol] -> *) (proxy :: * -> *)
                             . (A.Architecture arch,
                                HR.HasRepr a (A.ShapeRepr arch),
                                OrdF a,
                                ShowF a,
                                LF.LiftF a)
                   => proxy arch
                   -> (forall tp . L.Location arch tp -> Q Exp)
                   -- ^ A translation of 'L.Location' references into 'Exp's
                   -- that generate macaw IR to reference those expressions
                   -> (forall tp t . BoundVarInterpretations arch t -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                   -- ^ A translation of uninterpreted functions into macaw IR;
                   -- returns 'Nothing' if the handler does not know how to
                   -- translate the 'S.NonceApp'.
                   -> (forall tp t . BoundVarInterpretations arch t -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                   -- ^ Similarly, a translator for 'S.App's; mostly intended to
                   -- translate division operations into architecture-specific
                   -- statements, which have no representation in macaw.
                   -> Name
                   -- ^ The arch-specific instruction matcher for translating
                   -- instructions directly into macaw IR; this is usually used
                   -- for translating trap and system call type instructions.
                   -- This has to be specified by 'Name' instead of as a normal
                   -- function, as the type would actually refer to types that
                   -- we cannot mention in this shared code (i.e.,
                   -- architecture-specific instruction types).
                   -> [(Some a, BS.ByteString)]
                   -- ^ A list of opcodes (with constraint information
                   -- witnessed) paired with the bytestrings containing their
                   -- semantics.  This comes from semmc.
                   -> [Some (DT.CaptureInfo a)]
                   -- ^ Extra information for each opcode to let us generate
                   -- some TH to match them.  This comes from the semantics
                   -- definitions in semmc.
                   -> (Q Type, Q Type)
                   -> U.LogCfg
                   -- ^ Logging configuration (explicit rather than
                   -- the typical implicit expression because I don't
                   -- know how to pass implicits to TH splices
                   -- invocations.
                   -> Q Exp
genExecInstructionLogging _ ltr ena ae archInsnMatcher semantics captureInfo operandResultType logcfg =
    U.withLogCfg logcfg $ do
      Some ng <- runIO PN.newIONonceGenerator
      sym <- runIO (S.newSimpleBackend ng)
      formulas <- runIO (loadFormulas sym semantics)
      let formulasWithInfo = foldr (attachInfo formulas) Map.empty captureInfo
      instructionMatcher ltr ena ae archInsnMatcher formulasWithInfo operandResultType
        where
          attachInfo m0 (Some ci) m =
              let co = DT.capturedOpcode ci
              in case Map.lookup co m0 of
                   Nothing -> m
                   Just pf -> Map.insert co (PairF pf ci) m

natReprTH :: M.NatRepr w -> Q Exp
natReprTH w = [| knownNat :: M.NatRepr $(litT (numTyLit (natValue w))) |]

natReprFromIntTH :: Int -> Q Exp
natReprFromIntTH i = [| knownNat :: M.NatRepr $(litT (numTyLit (fromIntegral i))) |]

-- | Sequence a list of monadic actions without constructing an intermediate
-- list structure
doSequenceQ :: [StmtQ] -> [Stmt] -> Q Exp
doSequenceQ stmts body = doE (stmts ++ map return body)

translateFormula :: forall arch t sh .
                    (A.Architecture arch)
                 => (forall tp . L.Location arch tp -> Q Exp)
                 -> (forall tp . BoundVarInterpretations arch t -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                 -> (forall tp . BoundVarInterpretations arch t -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t Exp))
                 -> Name
                 -> ParameterizedFormula (Sym t) arch sh
                 -> BoundVarInterpretations arch t
                 -> SL.List (C.Const Name) sh
                 -> Q Exp
translateFormula ltr ena ae ipVarName semantics interps varNames = do
  let preamble = [ bindS (varP (regsValName interps)) [| G.getRegs |] ]
  exps <- runMacawQ ltr ena ae (mapM_ translateDefinition (Map.toList (pfDefs semantics)))
  [| Just $(doSequenceQ preamble exps) |]
  where translateDefinition :: Map.Pair (Parameter arch sh) (S.SymExpr (Sym t))
                            -> MacawQ arch t ()
        translateDefinition (Map.Pair param expr) = do
          case param of
            OperandParameter _w idx -> do
              let C.Const name = varNames SL.!! idx
              newVal <- addEltTH interps expr
              appendStmt [| G.setRegVal (O.toRegister $(varE name)) $(return newVal) |]
            LiteralParameter loc
              | L.isMemoryLocation loc -> writeMemTH interps expr
              | otherwise -> do
                  valExp <- addEltTH interps expr
                  appendStmt [| G.setRegVal $(ltr loc) $(return valExp) |]
            FunctionParameter str (WrappedOperand _ opIx) _w -> do
              let C.Const boundOperandName = varNames SL.!! opIx
              case lookup str (A.locationFuncInterpretation (Proxy @arch)) of
                Nothing -> fail ("Function has no definition: " ++ str)
                Just fi -> do
                  valExp <- addEltTH interps expr
                  appendStmt [| case $(varE (A.exprInterpName fi)) $(varE boundOperandName) of
                                   Just reg -> G.setRegVal (O.toRegister reg) $(return valExp)
                                   Nothing -> error ("Invalid instruction form at " ++ show $(varE ipVarName))
                               |]

addEltTH :: forall arch t ctp .
            (A.Architecture arch)
         => BoundVarInterpretations arch t
         -> S.Expr t ctp
         -> MacawQ arch t Exp
addEltTH interps elt = do
  mexp <- lookupElt elt
  case mexp of
    Just e -> return e
    Nothing ->
      case elt of
        S.BVExpr w val _loc ->
          bindExpr elt [| return (M.BVValue $(natReprTH w) $(lift val)) |]
        S.AppExpr appElt -> do
          translatedExpr <- appToExprTH (S.appExprApp appElt) interps
          bindExpr elt [| G.addExpr =<< $(return translatedExpr) |]
        S.BoundVarExpr bVar ->
          case Map.lookup bVar (locVars interps) of
            Just loc -> withLocToReg $ \ltr -> do
              bindExpr elt [| return ($(varE (regsValName interps)) ^. M.boundValue $(ltr loc)) |]
            Nothing  ->
              case Map.lookup bVar (opVars interps) of
                Just (C.Const name) -> bindExpr elt [| O.extractValue $(varE name) |]
                Nothing -> fail $ "bound var not found: " ++ show bVar
        S.NonceAppExpr n -> do
          translatedExpr <- evalNonceAppTH interps (S.nonceExprApp n)
          bindExpr elt (return translatedExpr)
        S.SemiRingLiteral {} -> liftQ [| error "SemiRingLiteral Elts are not supported" |]

symFnName :: S.ExprSymFn t args ret -> String
symFnName = T.unpack . Sy.solverSymbolAsText . S.symFnName

writeMemTH :: forall arch t tp
            . (A.Architecture arch)
           => BoundVarInterpretations arch t
           -> S.Expr t tp
           -> MacawQ arch t ()
writeMemTH bvi expr =
  case expr of
    S.NonceAppExpr n ->
      case S.nonceExprApp n of
        S.FnApp symFn args
          | Just memWidth <- matchWriteMemWidth (symFnName symFn) ->
            case FC.toListFC Some args of
              [_, Some addr, Some val] -> do
                addrValExp <- addEltTH bvi addr
                writtenValExp <- addEltTH bvi val
                appendStmt [| G.addStmt (M.WriteMem $(return addrValExp) (M.BVMemRepr $(natReprFromIntTH memWidth) M.BigEndian) $(return writtenValExp)) |]
              _ -> fail ("Invalid memory write expression: " ++ showF expr)
        _ -> fail ("Unexpected memory definition: " ++ showF expr)
    _ -> fail ("Unexpected memory definition: " ++ showF expr)

-- | Match a "write_mem" intrinsic and return the number of bytes written
matchWriteMemWidth :: String -> Maybe Int
matchWriteMemWidth s = do
  suffix <- L.stripPrefix "write_mem_" s
  (`div` 8) <$> readMaybe suffix

evalNonceAppTH :: forall arch t tp
                . (A.Architecture arch)
               => BoundVarInterpretations arch t
               -> S.NonceApp t (S.Expr t) tp
               -> MacawQ arch t Exp
evalNonceAppTH bvi nonceApp = do
  mtranslator <- withNonceAppEvaluator $ \evalNonceApp -> return (evalNonceApp bvi nonceApp)
  case mtranslator of
    Just translator -> translator
    Nothing -> defaultNonceAppEvaluator bvi nonceApp

defaultNonceAppEvaluator :: forall arch t tp
                          . (A.Architecture arch)
                         => BoundVarInterpretations arch t
                         -> S.NonceApp t (S.Expr t) tp
                         -> MacawQ arch t Exp
defaultNonceAppEvaluator bvi nonceApp =
  case nonceApp of
    S.FnApp symFn args -> do
      let fnName = symFnName symFn
      case fnName of
        "test_bit_dynamic" ->
          case FC.toListFC Some args of
            [Some bitNum, Some loc] -> do
              bitNumExp <- addEltTH bvi bitNum
              locExp <- addEltTH bvi loc
              liftQ [| G.addExpr (G.AppExpr (M.BVTestBit $(return bitNumExp) $(return locExp))) |]
            _ -> fail ("Unsupported argument list for test_bit_dynamic: " ++ showF args)
        -- For count leading zeros, we don't have a SimpleBuilder term to reduce
        -- it to, so we have to manually transform it to macaw here (i.e., we
        -- can't use the more general substitution method, since that is in
        -- terms of rewriting simplebuilder).
        "clz_32" ->
          case FC.toListFC Some args of
            [Some loc] -> do
              locExp <- addEltTH bvi loc
              liftQ [| G.addExpr (G.AppExpr (M.Bsr (NR.knownNat @32) $(return locExp))) |]
            _ -> fail ("Unsupported argument list for clz: " ++ showF args)
        "clz_64" ->
          case FC.toListFC Some args of
            [Some loc] -> do
              locExp <- addEltTH bvi loc
              liftQ [| G.addExpr (G.AppExpr (M.Bsr (NR.knownNat @64) $(return locExp))) |]
            _ -> fail ("Unsupported argument list for clz: " ++ showF args)
        "popcnt_32" ->
          case FC.toListFC Some args of
            [Some loc] -> do
              locExp <- addEltTH bvi loc
              liftQ [| G.addExpr (G.AppExpr (M.PopCount (NR.knownNat @32) $(return locExp))) |]
            _ -> fail ("Unsupported argument list for popcnt: " ++ showF args)
        "popcnt_64" ->
          case FC.toListFC Some args of
            [Some loc] -> do
              locExp <- addEltTH bvi loc
              liftQ [| G.addExpr (G.AppExpr (M.PopCount (NR.knownNat @64) $(return locExp))) |]
            _ -> fail ("Unsupported argument list for popcnt: " ++ showF args)
        "undefined" -> do
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
                addr <- addEltTH bvi addrElt
                liftQ [| let memRep = M.BVMemRepr (NR.knownNat :: NR.NatRepr $(litT (numTyLit (fromIntegral nBytes)))) M.BigEndian
                        in M.AssignedValue <$> G.addAssignment (M.ReadMem $(return addr) memRep)
                       |]
              _ -> fail ("Unexpected arguments to read_mem: " ++ showF args)
          | otherwise ->
            case lookup fnName (A.locationFuncInterpretation (Proxy @arch)) of
              Nothing -> error ("Unsupported UF: " ++ show fnName)
              Just fi -> do
                -- args is an assignment that contains elts; we could just generate
                -- expressions that evaluate each one and then splat them into new names
                -- that we apply our name to.
                case FC.toListFC (asName fnName bvi) args of
                  [] -> fail ("zero-argument uninterpreted functions are not supported: " ++ fnName)
                  argNames -> do
                    let call = appE (varE (A.exprInterpName fi)) $ foldr1 appE (map varE argNames)
                    liftQ [| O.extractValue ($(call)) |]
    _ -> error "Unsupported NonceApp case"

-- | Parse the name of a memory read intrinsic and return the number of bytes
-- that it reads.  For example
--
-- > readMemBytes "read_mem_8" == Just 1
readMemBytes :: String -> Maybe Int
readMemBytes s = do
  nBitsStr <- L.stripPrefix "read_mem_" s
  nBits <- readMaybe nBitsStr
  return (nBits `div` 8)

asName :: String -> BoundVarInterpretations arch t -> S.Expr t tp -> Name
asName ufName bvInterps elt =
  case elt of
    S.BoundVarExpr bVar ->
      case Map.lookup bVar (opVars bvInterps) of
        Nothing -> error ("Expected " ++ show bVar ++ " to have an interpretation")
        Just (C.Const name) -> name
    _ -> error ("Unexpected elt as name (" ++ showF elt ++ ") in " ++ ufName)

appToExprTH :: (A.Architecture arch)
            => S.App (S.Expr t) tp
            -> BoundVarInterpretations arch t
            -> MacawQ arch t Exp
appToExprTH app interps = do
  mtranslator <- withAppEvaluator $ \evalApp -> return (evalApp interps app)
  case mtranslator of
    Just translator -> translator
    Nothing -> defaultAppEvaluator app interps

defaultAppEvaluator :: (A.Architecture arch)
                    => S.App (S.Expr t) ctp
                    -> BoundVarInterpretations arch t
                    -> MacawQ arch t Exp
defaultAppEvaluator elt interps = case elt of
  S.TrueBool  -> liftQ [| return $ G.ValueExpr (M.BoolValue True) |]
  S.FalseBool -> liftQ [| return $ G.ValueExpr (M.BoolValue False) |]
  S.NotBool bool -> do
    e <- addEltTH interps bool
    liftQ [| return (G.AppExpr (M.NotApp $(return e))) |]
  S.AndBool bool1 bool2 -> do
    e1 <- addEltTH interps bool1
    e2 <- addEltTH interps bool2
    liftQ [| return (G.AppExpr (M.AndApp $(return e1) $(return e2))) |]
  S.XorBool bool1 bool2 -> do
    e1 <- addEltTH interps bool1
    e2 <- addEltTH interps bool2
    liftQ [| return (G.AppExpr (M.XorApp $(return e1) $(return e2))) |]
  S.IteBool test t f -> do
    testE <- addEltTH interps test
    tE <- addEltTH interps t
    fE <- addEltTH interps f
    liftQ [| return (G.AppExpr (M.Mux M.BoolTypeRepr $(return testE) $(return tE) $(return fE))) |]
  S.BVIte w _ test t f -> do
    testE <- addEltTH interps test
    tE <- addEltTH interps t
    fE <- addEltTH interps f
    liftQ [| return (G.AppExpr (M.Mux (M.BVTypeRepr $(natReprTH w)) $(return testE) $(return tE) $(return fE))) |]
  S.BVEq bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.Eq $(return e1) $(return e2))) |]
  S.BVSlt bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVSignedLt $(return e1) $(return e2))) |]
  S.BVUlt bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVUnsignedLt $(return e1) $(return e2))) |]
  S.BVConcat w bv1 bv2 -> do
    let u = S.bvWidth bv1
        v = S.bvWidth bv2
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| TR.bvconcat $(return e1) $(return e2) $(natReprTH v) $(natReprTH u) $(natReprTH w) |]
  S.BVSelect idx n bv -> do
    let w = S.bvWidth bv
    case natValue n + 1 <= natValue w of
      True -> do
        e <- addEltTH interps bv
        liftQ [| TR.bvselect $(return e) $(natReprTH n) $(natReprTH idx) $(natReprTH w) |]
      False -> do
        e <- addEltTH interps bv
        liftQ [| case testEquality $(natReprTH n) $(natReprTH w) of
                   Just Refl -> return (G.ValueExpr $(return e))
                   Nothing -> error "Invalid reprs for BVSelect translation"
               |]
  S.BVNeg w bv -> do
    bvValExp <- addEltTH interps bv
    liftQ [| let repW = $(natReprTH w)
             in G.AppExpr <$> (M.BVAdd repW <$> G.addExpr (G.AppExpr (M.BVComplement repW $(return bvValExp))) <*> pure (M.mkLit repW 1))
           |]
  S.BVTestBit idx bv -> do
    bvValExp <- addEltTH interps bv
    liftQ [| G.AppExpr <$> (M.BVTestBit <$> G.addExpr (G.ValueExpr (M.BVValue $(natReprTH (S.bvWidth bv)) $(lift idx))) <*> pure $(return bvValExp)) |]
  S.BVAdd w bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVAdd $(natReprTH w) $(return e1) $(return e2))) |]
  S.BVMul w bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVMul $(natReprTH w) $(return e1) $(return e2))) |]
  S.BVShl w bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVShl $(natReprTH w) $(return e1) $(return e2))) |]
  S.BVLshr w bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVShr $(natReprTH w) $(return e1) $(return e2))) |]
  S.BVAshr w bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVSar $(natReprTH w) $(return e1) $(return e2))) |]
  S.BVZext w bv -> do
    e <- addEltTH interps bv
    liftQ [| return (G.AppExpr (M.UExt $(return e) $(natReprTH w))) |]
  S.BVSext w bv -> do
    e <- addEltTH interps bv
    liftQ [| return (G.AppExpr (M.SExt $(return e) $(natReprTH w))) |]
  S.BVTrunc w bv -> do
    e <- addEltTH interps bv
    liftQ [| return (G.AppExpr (M.Trunc $(return e) $(natReprTH w))) |]
  S.BVBitNot w bv -> do
    e <- addEltTH interps bv
    liftQ [| return (G.AppExpr (M.BVComplement $(natReprTH w) $(return e))) |]
  S.BVBitAnd w bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVAnd $(natReprTH w) $(return e1) $(return e2))) |]
  S.BVBitOr w bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVOr $(natReprTH w) $(return e1) $(return e2))) |]
  S.BVBitXor w bv1 bv2 -> do
    e1 <- addEltTH interps bv1
    e2 <- addEltTH interps bv2
    liftQ [| return (G.AppExpr (M.BVXor $(natReprTH w) $(return e1) $(return e2))) |]
  _ -> error $ "unsupported Crucible elt:" ++ show elt

