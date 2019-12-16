{- |

This module defines a monad `Changed` that is designed for supporting
functions which take a value of some type as an argument, and may
modify it's value.

It is primarily used for abstract domains so that we know if we need
to re-explore a block when joining new edges into the state.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
module Data.Macaw.Utils.Changed
  ( Changed
  , runChanged
  , markChanged
  , changedST
  ) where

import           Control.Monad.Reader
import           Control.Monad.ST
import           Data.STRef

------------------------------------------------------------------------
-- Changed

-- | A monad that can be used to record when a value is changed.
newtype Changed s a = Changed { unChanged :: ReaderT (STRef s Bool) (ST s) a }
  deriving (Functor, Applicative, Monad)

-- | Run a `ST` computation.
changedST :: ST s a -> Changed s a
changedST m = Changed (lift m)

-- | Record the value has changed if the Boolean is true.
markChanged :: Bool -> Changed s ()
markChanged False = pure ()
markChanged True = do
  r <- Changed ask
  changedST $ writeSTRef r True

runChanged :: forall a . (forall s . Changed s a) -> Maybe a
runChanged action = runST $ do
  r <-  newSTRef False
  a <- runReaderT (unChanged action) r
  b <- readSTRef r
  pure $! if b then Just a else Nothing
