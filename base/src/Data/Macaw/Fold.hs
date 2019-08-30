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
  { foldCValue  :: !(forall tp . CValue arch tp -> r)
  , foldInput      :: !(forall utp . ArchReg arch utp -> r)
  , foldAssign     :: !(forall utp . AssignId ids utp -> r -> r)
  }

-- | Empty value fold returns mempty for each non-recursive fold, and the
-- identify of @foldAssign@
emptyValueFold :: Monoid r => ValueFold arch ids r
emptyValueFold =
  ValueFold { foldCValue = \_ -> mempty
            , foldInput  = \_ -> mempty
            , foldAssign = \_ r -> r
            }

-- | This folds over elements of a values in a  values.
--
-- It memoizes the results so that if an assignment is visited
-- multiple times, we only visit the children the first time it is
-- visited.  On subsequent visits, `foldAssign` will still be called,
-- but the children will not be revisited.
--
-- This makes the total time to visit linear with respect to the
-- number of children, but still allows determining whether a term is
-- shared.
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
        CValue c  ->
          pure $! foldCValue fns c
        AssignedValue (Assignment a rhs) -> do
          m <- get
          case Map.lookup (Some a) m of
            Just v' ->
              pure $! foldAssign fns a v'
            Nothing -> do
              rhsVal <- foldlMFC' (\s v' -> mappend s <$> go v') mempty rhs
              modify' $ Map.insert (Some a) rhsVal
              pure $! foldAssign fns a rhsVal
        Initial r    ->
          pure $! foldInput fns r
