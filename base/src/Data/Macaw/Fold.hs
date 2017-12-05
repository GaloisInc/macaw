{-
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This module provides a function for folding over the subexpressions in
a value without revisiting shared subterms.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Fold
  ( Data.Parameterized.TraversableFC.FoldableFC(..)
  , foldValueCached
  ) where

import           Control.Monad.State.Strict
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC

import           Data.Macaw.CFG

-- Helper that is a state monad, and also a monoid when the return value
-- is a monoid.
newtype MonadMonoid m a = MM { getMonadMonoid :: m a }
   deriving (Functor, Applicative, Monad)

instance MonadState s m => MonadState s (MonadMonoid m) where
  get = MM get
  put s = MM (put s)


instance (Applicative m, Monoid a) => Monoid (MonadMonoid m a) where
  mempty = pure mempty
  mappend m m' = mappend <$> m <*> m'

-- | This folds over elements of a values in a  values.
--
-- It memoizes values so that it only evaluates assignments with the same id
-- once.
foldValueCached :: forall m arch ids tp
                .  (Monoid m, FoldableFC (ArchFn arch))
                => (forall n.  NatRepr n -> Integer -> m)
                   -- ^ Function for literals
                -> (ArchMemAddr arch -> m)
                   -- ^ Function for memwords
                -> (forall utp . ArchReg arch utp -> m)
                   -- ^ Function for input registers
                -> (forall utp . AssignId ids utp -> m -> m)
                   -- ^ Function for assignments
                -> Value arch ids tp
                -> State (Map (Some (AssignId ids)) m) m
foldValueCached litf rwf initf assignf = getMonadMonoid . go
  where
    go :: forall tp'
       .  Value arch ids tp'
       -> MonadMonoid (State (Map (Some (AssignId ids)) m)) m
    go v =
      case v of
        BoolValue b -> return (litf (knownNat :: NatRepr 1) (if b then 1 else 0))
        BVValue sz i -> return $ litf sz i
        RelocatableValue _ a -> pure $ rwf a
        Initial r    -> return $ initf r
        AssignedValue (Assignment a_id rhs) -> do
          m <- get
          case Map.lookup (Some a_id) m of
            Just v' ->
              return $ assignf a_id v'
            Nothing -> do
              rhs_v <- foldMapFC go rhs
              modify' $ Map.insert (Some a_id) rhs_v
              return (assignf a_id rhs_v)
