{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeInType #-}
module Data.Macaw.SemMC.TH.Monad (
  MacawTHConfig(..),
  BoundVarInterpretations(..),
  BoundExp(..),
  MacawQ,
  runMacawQ,
  liftQ,
  lookupElt,
  appendStmt,
  withLocToReg,
  withNonceAppEvaluator,
  withAppEvaluator,
  bindExpr,
  letBindExpr,
  letBindPureExpr,
  bindTH,
  letTH,
  extractBound,
  refBinding,
  inConditionalContext,
  isTopLevel,
  definedFunction
  ) where

import qualified Control.Monad.Fail as MF
import qualified Control.Monad.State.Strict as St
import           Control.Monad.Trans ( lift )
import qualified Data.Functor.Const as C
import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Seq
import           Language.Haskell.TH

import qualified Data.Macaw.CFG as M
import qualified Data.Parameterized.Map as Map
import           Data.Parameterized.Some ( Some(..) )
import qualified Lang.Crucible.Backend.Simple as S
import qualified SemMC.Formula as SF
import qualified What4.Expr.Builder as S
import qualified What4.Interface as SI

import qualified SemMC.Architecture.Location as L

type Sym t fs = S.SimpleBackend t fs

data BoundVarInterpretations arch t fs =
  BoundVarInterpretations { locVars :: Map.MapF (SI.BoundVar (Sym t fs)) (L.Location arch)
                          , opVars  :: Map.MapF (SI.BoundVar (Sym t fs)) (C.Const Name)
                          , valVars :: Map.MapF (SI.BoundVar (Sym t fs)) (C.Const Name)
                          -- TODO If there's no worry about name conflicts,
                          -- combine all three into one map.
                          , regsValName :: Name
                          }

data MacawTHConfig arch opc t fs =
  MacawTHConfig { locationTranslator :: forall tp . L.Location arch tp -> Q Exp
                -- ^ A translation of 'L.Location' references into 'Exp's
                -- that generate macaw IR to reference those expressions
                , nonceAppTranslator :: forall tp . BoundVarInterpretations arch t fs -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t fs Exp)
                -- ^ A translation of uninterpreted functions into macaw IR;
                -- returns 'Nothing' if the handler does not know how to
                -- translate the 'S.NonceApp'.
                , appTranslator :: forall tp . BoundVarInterpretations arch t fs -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t fs Exp)
                -- ^ Similarly, a translator for 'S.App's; mostly intended to
                -- translate division operations into architecture-specific
                -- statements, which have no representation in macaw.
                , instructionMatchHook :: Name
                -- ^ The arch-specific instruction matcher for translating
                -- instructions directly into macaw IR; this is usually used
                -- for translating trap and system call type instructions.
                -- This has to be specified by 'Name' instead of as a normal
                -- function, as we insert calls to it via TH (which has to be
                -- done by name)
                , archEndianness :: M.Endianness
                -- ^ The endianness of the architecture we are translating.
                -- Note that it is fixed: we don't support endianness switching
                , operandTypeQ :: Q Type
                -- ^ A TH action to generate the operand type for the architecture
                , archTypeQ :: Q Type
                -- ^ A TH action to generate the type tag for the architecture
                , genLibraryFunction :: forall sym . Some (SF.FunctionFormula sym) -> Bool
                , genOpcodeCase :: forall tps . opc tps -> Bool
                }

data QState arch t fs = QState { accumulatedStatements :: !(Seq.Seq Stmt)
                            -- ^ The list of template haskell statements accumulated
                            -- for this monadic context.  At the end of the context, we
                            -- can extract these and wrap them in a @do@ expression.
                            , expressionCache :: !(M.Map (Some (S.Expr t)) Exp)
                            -- ^ A cache of translations of SimpleBuilder terms into
                            -- TH.  The cached values are not the translated exprs;
                            -- instead, they are names that are bound for those
                            -- terms (via 'VarE')
                            , lazyExpressionCache :: !(M.Map (Some (S.Expr t)) Exp)
                            -- ^ This is the same as expressionCache, except
                            -- that each expression is translated as a let
                            -- binding (that references its arguments in an
                            -- applicative style).
                            --
                            -- This supports translation of
                            -- conditionally-evaluated code (specifically,
                            -- ensuring that side effects only execute if
                            -- required).
                            , locToReg :: forall tp . L.Location arch tp -> Q Exp
                            , nonceAppEvaluator :: forall tp
                                                 . BoundVarInterpretations arch t fs
                                                -> S.NonceApp t (S.Expr t) tp
                                                -> Maybe (MacawQ arch t fs Exp)
                            -- ^ Convert SimpleBuilder NonceApps into Macaw expressions
                            , appEvaluator :: forall tp
                                            . BoundVarInterpretations arch t fs
                                           -> S.App (S.Expr t) tp
                                           -> Maybe (MacawQ arch t fs Exp)
                            , definedFunctionEvaluator :: String
                                                       -> Maybe (MacawQ arch t fs Exp)
                            , translationDepth :: !Int
                            -- ^ At depth 0, we are translating at the top level
                            -- (and should eagerly bind side-effecting
                            -- operations).  At higher depths we are inside of
                            -- conditionals and should use lazy binding.
                            }

emptyQState :: MacawTHConfig arch opc t fs
            -> (String -> Maybe (MacawQ arch t fs Exp))
            -> QState arch t fs
emptyQState thConf df = QState { accumulatedStatements = Seq.empty
                               , expressionCache = M.empty
                               , lazyExpressionCache = M.empty
                               , locToReg = locationTranslator thConf
                               , nonceAppEvaluator = nonceAppTranslator thConf
                               , appEvaluator = appTranslator thConf
                               , definedFunctionEvaluator = df
                               , translationDepth = 0
                               }

newtype MacawQ arch t fs a = MacawQ { unQ :: St.StateT (QState arch t fs) Q a }
  deriving (Functor,
            Applicative,
            Monad,
            MF.MonadFail,
            St.MonadState (QState arch t fs))

runMacawQ :: MacawTHConfig arch opc t fs
          -> (String -> Maybe (MacawQ arch t fs Exp))
          -> MacawQ arch t fs ()
          -> Q [Stmt]
runMacawQ thConf df act = (F.toList . accumulatedStatements) <$> St.execStateT (unQ act) (emptyQState thConf df)

isTopLevel :: MacawQ arch t fs Bool
isTopLevel = (==0) <$> St.gets translationDepth

inConditionalContext :: MacawQ arch t fs a
                     -> MacawQ arch t fs a
inConditionalContext k = do
  St.modify' $ \s -> s { translationDepth = translationDepth s + 1 }
  res <- k
  St.modify' $ \s -> s { translationDepth = translationDepth s - 1 }
  return res

-- | Lift a TH computation (in the 'Q' monad) into the monad.
liftQ :: Q a -> MacawQ arch t fs a
liftQ q = MacawQ (lift q)

withLocToReg :: ((L.Location arch tp -> Q Exp) -> MacawQ arch t fs a) -> MacawQ arch t fs a
withLocToReg k = do
  f <- St.gets locToReg
  k f

-- | Look up an 'S.Expr' in the cache
lookupElt :: S.Expr t tp -> MacawQ arch t fs (Maybe BoundExp)
lookupElt elt = do
  c <- St.gets expressionCache
  case M.lookup (Some elt) c of
    Just e -> return (Just (EagerBoundExp e))
    Nothing -> do
      lc <- St.gets lazyExpressionCache
      return (LazyBoundExp <$> M.lookup (Some elt) lc)

withNonceAppEvaluator :: forall tp arch t fs
                       . ((BoundVarInterpretations arch t fs -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t fs Exp)) -> MacawQ arch t fs (Maybe (MacawQ arch t fs Exp)))
                      -> MacawQ arch t fs (Maybe (MacawQ arch t fs Exp))
withNonceAppEvaluator k = do
  nae <- St.gets nonceAppEvaluator
  k nae

withAppEvaluator :: forall tp arch t fs
                  . ((BoundVarInterpretations arch t fs -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t fs Exp)) -> MacawQ arch t fs (Maybe (MacawQ arch t fs Exp)))
                 -> MacawQ arch t fs (Maybe (MacawQ arch t fs Exp))
withAppEvaluator k = do
  ae <- St.gets appEvaluator
  k ae

-- | Append a statement that doesn't need to bind a new name
appendStmt :: ExpQ -> MacawQ arch t fs ()
appendStmt eq = do
  e <- liftQ eq
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> NoBindS e }

-- | A wrapper around a TH 'Exp' that records how it was bound in its current
-- context, letting a holder of a 'BoundExp' know how to evaluate it
data BoundExp where
  -- | The 'Exp' represents a let bound 'Generator' action (and needs to be sequenced to evaluate it)
  LazyBoundExp :: Exp -> BoundExp
  -- | The 'Exp' represents an actual run-time macaw Value
  EagerBoundExp :: Exp -> BoundExp

-- | Bind a TH expression to a name (as a 'Stmt') and return the expression that
-- refers to the bound value.  For example, if you call
--
-- > bindExpr [| return (1 + 2) |]
--
-- The statement added to the state is
--
-- > newName <- expr
--
-- and the new name is returned.
bindExpr :: S.Expr t tp -> ExpQ -> MacawQ arch t fs BoundExp
bindExpr elt eq = do
  e <- liftQ eq
  n <- liftQ (newName "val")
  let res = VarE n
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> BindS (VarP n) e
                       , expressionCache = M.insert (Some elt) res (expressionCache s)
                       }
  return (EagerBoundExp res)

letBindPureExpr :: S.Expr t tp -> ExpQ -> MacawQ arch t fs BoundExp
letBindPureExpr elt eq = do
  e <- liftQ eq
  n <- liftQ (newName "lval")
  let res = VarE n
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> LetS [ValD (VarP n) (NormalB e) []]
                       , expressionCache = M.insert (Some elt) res (expressionCache s)
                       }
  return (EagerBoundExp res)

letBindExpr :: S.Expr t tp -> Exp -> MacawQ arch t fs BoundExp
letBindExpr elt e = do
  n <- liftQ (newName "lval")
  let res = VarE n
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> LetS [ValD (VarP n) (NormalB e) []]
                       , lazyExpressionCache = M.insert (Some elt) res (lazyExpressionCache s)
                       }
  return (LazyBoundExp res)

letTH :: ExpQ -> MacawQ arch t fs BoundExp
letTH eq = do
  e <- liftQ eq
  n <- liftQ (newName "lval")
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> LetS [ValD (VarP n) (NormalB e) []]
                       }
  return (LazyBoundExp (VarE n))

bindTH :: ExpQ -> MacawQ arch t fs BoundExp
bindTH eq = do
  e <- liftQ eq
  n <- liftQ (newName "bval")
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> BindS (VarP n) e
                       }
  return (EagerBoundExp (VarE n))

definedFunction :: String -> MacawQ arch t fs (Maybe Exp)
definedFunction name = do
  df <- St.gets definedFunctionEvaluator
  case df name of
    Just expr -> Just <$> expr
    Nothing -> return Nothing

extractBound :: BoundExp -> MacawQ arch t fs Exp
extractBound be =
  case be of
    LazyBoundExp e -> liftQ [| $(return e) |]
    EagerBoundExp e -> liftQ [| pure $(return e) |]

-- | Like 'extractBound', but for use inside of TH splices
refBinding :: BoundExp -> Q Exp
refBinding be =
  case be of
    -- In this case, we already have an evaluated expression so we just inject
    -- it into the context with 'pure'
    EagerBoundExp e -> [| pure $(return e) |]
    -- If it is lazy, we need it "bare" in the applicative wrappers
    LazyBoundExp e -> return e
