{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Macaw.SemMC.TH.Monad (
  BoundVarInterpretations(..),
  MacawQ,
  runMacawQ,
  liftQ,
  lookupElt,
  appendStmt,
  withLocToReg,
  withNonceAppEvaluator,
  withAppEvaluator,
  cacheExpr,
  bindExpr,
  bindTH,
  letTH,
  inLocalBlock,
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

import qualified Data.Parameterized.Map as Map
import           Data.Parameterized.Some ( Some(..) )
import qualified Lang.Crucible.Backend.Simple as S
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

data QState arch t fs = QState { accumulatedStatements :: !(Seq.Seq Stmt)
                            -- ^ The list of template haskell statements accumulated
                            -- for this monadic context.  At the end of the context, we
                            -- can extract these and wrap them in a @do@ expression.
                            , expressionCache :: !(M.Map (Some (S.Expr t)) Exp)
                            -- ^ A cache of translations of SimpleBuilder terms into
                            -- TH.  The cached values are not the translated exprs;
                            -- instead, they are names that are bound for those
                            -- terms (via 'VarE')
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
                            }

emptyQState :: (forall tp . L.Location arch tp -> Q Exp)
            -> (forall tp . BoundVarInterpretations arch t fs -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t fs Exp))
            -> (forall tp . BoundVarInterpretations arch t fs -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t fs Exp))
            -> (String -> Maybe (MacawQ arch t fs Exp))
            -> QState arch t fs
emptyQState ltr ena ae df = QState { accumulatedStatements = Seq.empty
                                   , expressionCache = M.empty
                                   , locToReg = ltr
                                   , nonceAppEvaluator = ena
                                   , appEvaluator = ae
                                   , definedFunctionEvaluator = df
                                   }

newtype MacawQ arch t fs a = MacawQ { unQ :: St.StateT (QState arch t fs) Q a }
  deriving (Functor,
            Applicative,
            Monad,
            MF.MonadFail,
            St.MonadState (QState arch t fs))

runMacawQ :: (forall tp . L.Location arch tp -> Q Exp)
          -> (forall tp . BoundVarInterpretations arch t fs -> S.NonceApp t (S.Expr t) tp -> Maybe (MacawQ arch t fs Exp))
          -> (forall tp . BoundVarInterpretations arch t fs -> S.App (S.Expr t) tp -> Maybe (MacawQ arch t fs Exp))
          -> (String -> Maybe (MacawQ arch t fs Exp))
          -> MacawQ arch t fs ()
          -> Q [Stmt]
runMacawQ ltr ena ea df act = (F.toList . accumulatedStatements) <$> St.execStateT (unQ act) (emptyQState ltr ena ea df)

-- | This combinator creates a new scope of statement accumulation so that we
-- can make blocks of code in a @do@ block in the 'Generator' monad.
--
-- These can be used to create blocks that are conditionally-evaluated.  The
-- return value is a TH expression that is a @do@ block containing all of the
-- generated statements under the given local computation.
--
-- Note that we don't make any specific provisions for error handling/cleanup -
-- errors should just trigger TH errors at compile time.
--
-- Note that we make a fresh expression cache to ensure that we don't end up
-- with scoping issues.
inLocalBlock :: MacawQ arch t fs Exp
             -- ^ A computation that generates statements in a fresh block
             -> MacawQ arch t fs Exp
inLocalBlock k = do
  savedState <- St.get
  St.modify' $ \s -> s { accumulatedStatements = Seq.empty
                       }
  res <- k
  blockStmts <- St.gets accumulatedStatements
  ret <- liftQ $ noBindS [| return $(return res) |]
  -- St.put savedState
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements savedState }
  return (DoE (F.toList blockStmts ++ [ret]))


-- | Lift a TH computation (in the 'Q' monad) into the monad.
liftQ :: Q a -> MacawQ arch t fs a
liftQ q = MacawQ (lift q)

withLocToReg :: ((L.Location arch tp -> Q Exp) -> MacawQ arch t fs a) -> MacawQ arch t fs a
withLocToReg k = do
  f <- St.gets locToReg
  k f

-- | Look up an 'S.Expr' in the cache
lookupElt :: S.Expr t tp -> MacawQ arch t fs (Maybe Exp)
lookupElt elt = do
  c <- St.gets expressionCache
  return (M.lookup (Some elt) c)

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
bindExpr :: S.Expr t tp -> ExpQ -> MacawQ arch t fs Exp
bindExpr elt eq = do
  e <- liftQ eq
  n <- liftQ (newName "val")
  let res = VarE n
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> BindS (VarP n) e
                       , expressionCache = M.insert (Some elt) res (expressionCache s)
                       }
  return res

cacheExpr :: S.Expr t tp -> Exp -> MacawQ arch t fs ()
cacheExpr elt e = do
  St.modify' $ \s -> s { expressionCache = M.insert (Some elt) e (expressionCache s) }

letTH :: ExpQ -> MacawQ arch t fs Exp
letTH eq = do
  e <- liftQ eq
  n <- liftQ (newName "lval")
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> LetS [ValD (VarP n) (NormalB e) []]
                       }
  return (VarE n)

bindTH :: ExpQ -> MacawQ arch t fs Exp
bindTH eq = do
  e <- liftQ eq
  n <- liftQ (newName "bval")
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> BindS (VarP n) e
                       }
  return (VarE n)

definedFunction :: String -> MacawQ arch t fs (Maybe Exp)
definedFunction name = do
  df <- St.gets definedFunctionEvaluator
  case df name of
    Just expr -> Just <$> expr
    Nothing -> return Nothing
