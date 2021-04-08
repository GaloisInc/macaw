{-|
This defines types for performing a computation that
log progress incrementally before completing.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Macaw.Utils.IncComp
  ( IncComp(..)
  , incCompResult
  , processIncCompLogs
  , IncCompM(..)
  , runIncCompM
  , liftIncComp
  , joinIncComp
  , incCompLog
  , incCompDone
  , ContT(..)
  ) where

import Control.Monad.Cont ( cont, runCont, Cont, ContT(..) )

-- | @IncComp l r@ is an incremental computation.
--
-- This is effectively a lazy list of @l@ values terminated by an @r@ value.
data IncComp l r
    -- | Log a message
  = IncCompLog !l (IncComp l r)
    -- | Computation complete.
  | IncCompDone !r

incCompResult :: IncComp l r -> r
incCompResult (IncCompLog _ r) = incCompResult r
incCompResult (IncCompDone r) = r

joinIncComp :: (l -> k) -> (a -> IncComp k b) -> IncComp l a -> IncComp k b
joinIncComp f g m0 = do
  case m0 of
    IncCompLog l m -> IncCompLog (f l) (joinIncComp f g m)
    IncCompDone r -> g r

processIncCompLogs :: Monad m => (l -> m ()) -> IncComp l r -> m r
processIncCompLogs _ (IncCompDone r) = pure r
processIncCompLogs f (IncCompLog l r) = f l *> processIncCompLogs f r

-- | Continuation monad that yields an incremental computation.
newtype IncCompM l r a = IncCompTM { _unIncCompTM :: Cont (IncComp l r) a }
  deriving (Functor, Applicative, Monad)

runIncCompM :: IncCompM l r r -> IncComp l r
runIncCompM (IncCompTM m) = runCont m IncCompDone

-- | Log a warning
incCompLog :: l -> IncCompM l r ()
incCompLog msg = IncCompTM $ cont $ \f -> IncCompLog msg (f ())

-- | Terminate computation early.
incCompDone :: r -> IncCompM l r a
incCompDone e = IncCompTM $ cont $ \_ -> IncCompDone e

-- | Lift a incremental computation to the monad with the given modification
liftIncComp :: (l -> k) -> IncComp l a -> IncCompM k r a
liftIncComp f m = IncCompTM $ cont $ \c -> joinIncComp f c m