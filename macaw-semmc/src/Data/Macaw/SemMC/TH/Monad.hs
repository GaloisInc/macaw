{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Data.Macaw.SemMC.TH.Monad (
  MacawQ,
  runMacawQ,
  liftQ,
  lookupElt,
  appendStmt,
  withLocToReg,
  bindExpr
  ) where

import qualified Control.Monad.State.Strict as St
import           Control.Monad.Trans ( lift )
import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Seq
import           Language.Haskell.TH

import           Data.Parameterized.Some ( Some(..) )
import qualified Lang.Crucible.Solver.SimpleBuilder as S
import qualified SemMC.Architecture.Location as L

data QState arch t = QState { accumulatedStatements :: !(Seq.Seq Stmt)
                            -- ^ The list of template haskell statements accumulated
                            -- for this monadic context.  At the end of the context, we
                            -- can extract these and wrap them in a @do@ expression.
                            , expressionCache :: !(M.Map (Some (S.Elt t)) Exp)
                            -- ^ A cache of translations of SimpleBuilder terms into
                            -- TH.  The cached values are not the translated exprs;
                            -- instead, they are names that are bound for those
                            -- terms (via 'VarE')
                            , locToReg :: forall tp . L.Location arch tp -> Q Exp
                            }

emptyQState :: (forall tp . L.Location arch tp -> Q Exp) -> QState arch t
emptyQState ltr = QState { accumulatedStatements = Seq.empty
                         , expressionCache = M.empty
                         , locToReg = ltr
                         }

newtype MacawQ arch t a = MacawQ { unQ :: St.StateT (QState arch t) Q a }
  deriving (Functor,
            Applicative,
            Monad,
            St.MonadState (QState arch t))

runMacawQ :: (forall tp . L.Location arch tp -> Q Exp) -> MacawQ arch t () -> Q [Stmt]
runMacawQ ltr act = (F.toList . accumulatedStatements) <$> St.execStateT (unQ act) (emptyQState ltr)

-- | Lift a TH computation (in the 'Q' monad) into the monad.
liftQ :: Q a -> MacawQ arch t a
liftQ q = MacawQ (lift q)

withLocToReg :: ((L.Location arch tp -> Q Exp) -> MacawQ arch t a) -> MacawQ arch t a
withLocToReg k = do
  f <- St.gets locToReg
  k f

-- | Look up an 'S.Elt' in the cache
lookupElt :: S.Elt t tp -> MacawQ arch t (Maybe Exp)
lookupElt elt = do
  c <- St.gets expressionCache
  return (M.lookup (Some elt) c)

-- | Append a statement that doesn't need to bind a new name
appendStmt :: ExpQ -> MacawQ arch t ()
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
bindExpr :: S.Elt t tp -> ExpQ -> MacawQ arch t Exp
bindExpr elt eq = do
  e <- liftQ eq
  n <- liftQ (newName "val")
  let res = VarE n
  St.modify' $ \s -> s { accumulatedStatements = accumulatedStatements s Seq.|> BindS (VarP n) e
                       , expressionCache = M.insert (Some elt) res (expressionCache s)
                       }
  return res
