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

-- | This folds over elements of a values in a  values.
--
-- It memoizes values so that it only evaluates assignments with the same id
-- once.
foldValueCached :: forall r arch ids tp
                .  (Monoid r, FoldableFC (ArchFn arch))
                => (forall n.  NatRepr n -> Integer -> r)
                   -- ^ Function for literals
                -> (ArchMemAddr arch -> r)
                   -- ^ Function for memwords
                -> (forall utp . ArchReg arch utp -> r)
                   -- ^ Function for input registers
                -> (forall utp . AssignId ids utp -> r -> r)
                   -- ^ Function for assignments
                -> Value arch ids tp
                -> State (Map (Some (AssignId ids)) r) r
foldValueCached litf rwf initf assignf = go
  where
    go :: forall tp'
       .  Value arch ids tp'
       -> State (Map (Some (AssignId ids)) r) r
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
              rhs_v <- foldrFC (\v' mrhs -> mappend <$> go v' <*> mrhs) (pure mempty) rhs
              modify' $ Map.insert (Some a_id) rhs_v
              return (assignf a_id rhs_v)
