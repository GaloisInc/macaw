{-
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This module provides a function for folding over the subexpressions in
a value without revisiting shared subterms.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Fold
  ( Data.Parameterized.TraversableFC.FoldableFC(..)
  , ValueFold(..)
  , emptyValueFold
  , foldValueCached
  ) where

import           Control.Monad.State.Strict
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC

import           Data.Macaw.CFG

data ValueFold arch ids r = ValueFold
  { foldBoolValue  :: !(Bool -> r)
  , foldBVValue    :: !(forall n . NatRepr n -> Integer -> r)
  , foldAddr       :: !(ArchMemAddr arch -> r)
  , foldIdentifier :: !(SymbolIdentifier -> r)
  , foldInput      :: !(forall utp . ArchReg arch utp -> r)
  , foldAssign     :: !(forall utp . AssignId ids utp -> r -> r)
  }

-- | Empty value fold returns mempty for each non-recursive fold, and the
-- identify of @foldAssign@
emptyValueFold :: Monoid r => ValueFold arch ids r
emptyValueFold =
  ValueFold { foldBoolValue  = \_ -> mempty
            , foldBVValue    = \_ _ -> mempty
            , foldAddr       = \_ -> mempty
            , foldIdentifier = \_ -> mempty
            , foldInput      = \_ -> mempty
            , foldAssign     = \_ r -> r
            }

-- | This folds over elements of a values in a  values.
--
-- It memoizes values so that it only evaluates assignments with the same id
-- once.
foldValueCached :: forall r arch ids tp
                .  (Monoid r, FoldableFC (ArchFn arch))
                => ValueFold arch ids r
                -> Value arch ids tp
                -> State (Map (Some (AssignId ids)) r) r
foldValueCached fns = go
  where
    go :: forall tp'
       .  Value arch ids tp'
       -> State (Map (Some (AssignId ids)) r) r
    go v =
      case v of
        BoolValue b  ->
          pure $! foldBoolValue fns b
        BVValue sz i ->
          pure $! foldBVValue fns sz i
        RelocatableValue _ a ->
          pure $! foldAddr fns a
        SymbolValue _ a ->
          pure $! foldIdentifier fns a
        Initial r    ->
          pure $! foldInput fns r
        AssignedValue (Assignment a_id rhs) -> do
          m <- get
          case Map.lookup (Some a_id) m of
            Just v' ->
              pure $! foldAssign fns a_id v'
            Nothing -> do
              rhs_v <- foldrFC (\v' mrhs -> mappend <$> go v' <*> mrhs) (pure mempty) rhs
              modify' $ Map.insert (Some a_id) rhs_v
              pure $! foldAssign fns a_id rhs_v
