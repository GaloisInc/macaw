{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Macaw.AbsDomain.JumpBounds
  ( InitialIndexBounds
  , arbitraryInitialBounds
  , joinInitialBounds
  , IndexBounds
  , mkIndexBounds
  , UpperBound(..)
  , addUpperBound
  , assertPred
  , unsignedUpperBound
  , nextBlockBounds
  ) where

import           Control.Lens
import           Control.Monad.State
import           Data.Functor
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.CFG
import           Data.Macaw.Types

-- | An upper bound on a value.
data UpperBound tp where
  -- | @IntegerUpperBound b v@ indicates the low @b@ bits of the value
  -- are at most @v@ when the bitvector is treated as an unsigned
  -- integer.
  UBVUpperBound :: (u <= w) => !(NatRepr u) -> !Natural -> UpperBound (BVType w)

instance Eq (UpperBound tp) where
  UBVUpperBound u x == UBVUpperBound v y =
    case testEquality u v of
      Nothing -> False
      Just Refl -> x == y

instance MapF.EqF UpperBound where
  eqF = (==)

instance Ord (UpperBound tp) where
  compare (UBVUpperBound u x) (UBVUpperBound v y) =
    case compareF u v of
      LTF -> LT
      EQF -> compare x y
      GTF -> GT

deriving instance Show (UpperBound tp)

-- | Bounds for a function as the start of a block.
data InitialIndexBounds r
   = InitialIndexBounds { initialRegUpperBound :: !(MapF r UpperBound)
                        }

instance MapF.TestEquality r => Eq (InitialIndexBounds r) where
   x == y = initialRegUpperBound x == initialRegUpperBound y

instance ShowF r => Pretty (InitialIndexBounds r) where
  pretty r = vcat $ ppPair <$> MapF.toList (initialRegUpperBound r)
    where ppPair :: MapF.Pair r UpperBound -> Doc
          ppPair (MapF.Pair k (UBVUpperBound w b)) =
            text (showF k) <> text ":[" <> text (show w) <> text "] <= " <> text (show b)

-- | Create initial index bounds that can represent any system state.
arbitraryInitialBounds :: InitialIndexBounds reg
arbitraryInitialBounds = InitialIndexBounds { initialRegUpperBound = MapF.empty }


type Changed = State Bool

-- | Record the value has changed if the Boolean is true.
markChanged :: Bool -> Changed ()
markChanged b = modify (|| b)

runChanged :: Changed a -> Maybe a
runChanged action =
  case runState action False of
    (r, True)  -> Just r
    (_, False) -> Nothing

-- | Take the union of two index bounds
joinInitialBounds :: forall r
                  .  MapF.OrdF r
                  => InitialIndexBounds r
                  -> InitialIndexBounds r
                  -> Maybe (InitialIndexBounds r)
joinInitialBounds old new = runChanged $ do
  let combineF :: r tp -> UpperBound tp -> UpperBound tp -> Changed (Maybe (UpperBound tp))
      combineF _ (UBVUpperBound u x) (UBVUpperBound v y) =
        case testEquality u v of
          Just Refl ->
            markChanged (x < y) $> Just (UBVUpperBound u (max x y))
          Nothing ->
            markChanged True $> Nothing

      -- Mark upper bounds exclusively in old set.
      -- If we have any only-old bounds add mark value as changed.
      oldF :: MapF r UpperBound -> Changed (MapF r UpperBound)
      oldF m = markChanged (not (MapF.null m)) $> MapF.empty

      -- How to upper bounds exclusively in new set.
      -- Drop any only-new bounds.
      newF :: MapF r UpperBound -> Changed (MapF r UpperBound)
      newF _ = pure MapF.empty

  z <- MapF.mergeWithKeyM combineF oldF newF (initialRegUpperBound old) (initialRegUpperBound new)
  pure InitialIndexBounds { initialRegUpperBound = z }

-- | Information about bounds for a particular value within a block.
data IndexBounds reg ids
   = IndexBounds { _regBounds :: !(MapF reg UpperBound)
                 , _assignUpperBound :: !(MapF (AssignId ids) UpperBound)
                 }

-- | Maps assignment ids to the associated upper bounds
regBounds :: Simple Lens (IndexBounds reg ids) (MapF reg UpperBound)
regBounds = lens _regBounds (\s v -> s { _regBounds = v })

-- | Maps assignment ids to the associated upper bounds
assignUpperBound :: Simple Lens (IndexBounds reg ids) (MapF (AssignId ids) UpperBound)
assignUpperBound = lens _assignUpperBound (\s v -> s { _assignUpperBound = v })

-- | Create index bounds from initial index bounds.
mkIndexBounds :: InitialIndexBounds reg -> IndexBounds reg ids
mkIndexBounds i = IndexBounds { _regBounds = initialRegUpperBound i
                              , _assignUpperBound = MapF.empty
                              }

-- | Add a inclusive upper bound to a value.
--
-- Our operation allows one to set the upper bounds on the low order
-- of an integer.  This is represented by the extra argument `NatRepr
-- u`.
--
-- This either returns the refined bounds, or `Left msg` where `msg`
-- is an explanation of what inconsistency was detected.  The upper
-- bounds must be non-negative.
addUpperBound :: ( MapF.OrdF (ArchReg arch)
                 , HasRepr (ArchReg arch) TypeRepr
                 , u <= w
                 )
               => BVValue arch ids w
                 -- ^ Value we are adding upper bound for.
               -> NatRepr u
                  -- ^ Restrict upper bound to only `u` bits.
               -> Natural
               -- ^ Upper bound as an unsigned number
               -> IndexBounds (ArchReg arch) ids
                 -- ^ Current bounds.
               -> Either String (IndexBounds (ArchReg arch) ids)
addUpperBound v u bnd bnds
    -- Do nothing if upper bounds equals or exceeds function
  | bnd >= fromInteger (maxUnsigned (typeWidth v)) = Right bnds
  | otherwise =
  case v of
    BVValue _ c | c <= toInteger bnd -> Right bnds
                | otherwise -> Left "Constant given upper bound that is statically less than given bounds"
    RelocatableValue{} -> Right bnds
    SymbolValue{}      -> Right bnds
    AssignedValue a ->
      case assignRhs a of
        EvalApp (UExt x _) ->
          case testLeq u (typeWidth x) of
            Just LeqProof -> addUpperBound x u bnd bnds
            Nothing ->
              case leqRefl (typeWidth x) of
                LeqProof -> addUpperBound x (typeWidth x) bnd bnds
        EvalApp (Trunc x w) ->
          case testLeq u w of
            Just LeqProof -> do
              case testLeq u (typeWidth x) of
                Just LeqProof -> addUpperBound x u bnd bnds
                Nothing -> error "addUpperBound invariant broken"
            Nothing -> do
              case testLeq w (typeWidth x) of
                Just LeqProof -> addUpperBound x w bnd bnds
                Nothing -> error "addUpperBound invariant broken"
        _ ->
          Right $ bnds & assignUpperBound %~ MapF.insertWith min (assignId a) (UBVUpperBound u bnd)
    Initial r ->
      Right $ bnds & regBounds %~ MapF.insertWith min r (UBVUpperBound u bnd)


-- | Assert a predicate is true/false and update bounds.
--
-- If it returns a new upper bounds, then that may be used.
-- Otherwise, it detects an inconsistency and returns a message
-- explaing why.
assertPred :: ( OrdF (ArchReg arch)
              , HasRepr (ArchReg arch) TypeRepr
              )
           => Value arch ids BoolType -- ^ Value represnting predicate
           -> Bool -- ^ Controls whether predicate is true or false
           -> IndexBounds (ArchReg arch) ids -- ^ Current index bounds
           -> Either String (IndexBounds (ArchReg arch) ids)
assertPred (AssignedValue a) isTrue bnds =
  case assignRhs a of
    -- Given x < c), assert x <= c-1
    EvalApp (BVUnsignedLt x (BVValue _ c))
      | isTrue     ->
        if c > 0 then
          addUpperBound x (typeWidth x) (fromInteger (c-1)) bnds
         else
          Left "x < 0 must be false."
    -- Given not (c < y), assert y <= c
    EvalApp (BVUnsignedLt (BVValue _ c) y)
      | not isTrue -> addUpperBound y (typeWidth y) (fromInteger c) bnds
    -- Given x <= c, assert x <= c
    EvalApp (BVUnsignedLe x (BVValue _ c))
      | isTrue     -> addUpperBound x (typeWidth x) (fromInteger c) bnds
    -- Given not (c <= y), assert y <= (c-1)
    EvalApp (BVUnsignedLe (BVValue _ c) y) | not isTrue ->
      if c > 0 then
        addUpperBound y (typeWidth y) (fromInteger (c-1)) bnds
       else
        Left "0 <= x cannot be false"
    -- Given x && y, assert x, then assert y
    EvalApp (AndApp l r) | isTrue     -> (assertPred l True >=> assertPred r True) bnds
    -- Given not (x || y), assert not x, then assert not y
    EvalApp (OrApp  l r) | not isTrue -> (assertPred l False >=> assertPred r False) bnds
    EvalApp (NotApp p) -> assertPred p (not isTrue) bnds
    _ -> Right bnds
assertPred _ _ bnds = Right bnds

-- | Lookup an upper bound or return analysis for why it is not defined.
unsignedUpperBound :: ( MapF.OrdF (ArchReg arch)
                      , MapF.ShowF (ArchReg arch)
                      , RegisterInfo (ArchReg arch)
                      )
                  => IndexBounds (ArchReg arch) ids
                  -> Value arch ids tp
                  -> Either String (UpperBound tp)
unsignedUpperBound bnds v =
  case v of
    BoolValue _ -> Left "Boolean values do not have bounds."
    BVValue w i -> Right $! UBVUpperBound w (fromInteger i)
    RelocatableValue{} ->
      Left "Relocatable values do not have bounds."
    SymbolValue{} ->
      Left "Symbol values do not have bounds."
    AssignedValue a ->
      case MapF.lookup (assignId a) (bnds^.assignUpperBound) of
        Just bnd -> Right bnd
        Nothing ->
          case assignRhs a of
            EvalApp (BVAnd _ x y) -> do
              case (unsignedUpperBound bnds x,  unsignedUpperBound bnds y) of
                (Right (UBVUpperBound xw xb), Right (UBVUpperBound yw yb))
                  | Just Refl <- testEquality xw yw ->
                    Right (UBVUpperBound xw (min xb yb))
                (Right xb, _) -> Right xb
                (Left{}, yb)       -> yb
            EvalApp (SExt x w) -> do
              UBVUpperBound u b <- unsignedUpperBound bnds x
              case testLeq u w of
                Just LeqProof -> pure $! UBVUpperBound u b
                Nothing -> error "unsignedUpperBound given bad width"
            EvalApp (UExt x w) -> do
              UBVUpperBound u r <- unsignedUpperBound bnds x
              -- If bound is full width, then we can keep it, otherwise we only have subset.
              case testEquality u (typeWidth x) of
                Just Refl -> pure $! UBVUpperBound w r
                Nothing ->
                  case testLeq u w of
                    Just LeqProof -> pure $! UBVUpperBound u r
                    Nothing -> error "unsignedUpperBound given bad width"
            EvalApp (Trunc x w) -> do
              UBVUpperBound u xr <- unsignedUpperBound bnds x
              case testLeq u w of
                Just LeqProof -> do
                  pure $! UBVUpperBound u xr
                Nothing -> do
                  pure $! UBVUpperBound w (min xr (fromInteger (maxUnsigned w)))
            _ -> Left $ "Could not find upper bounds for " ++ show (assignId a) ++ "."
    Initial r ->
      case MapF.lookup r (bnds^.regBounds) of
        Just bnd -> Right bnd
        Nothing -> Left $ "No upper bounds for " ++ showF r ++ "."

eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe (Right v) = Just v
eitherToMaybe Left{}    = Nothing


nextBlockBounds :: forall arch ids
                .  ( MapF.OrdF (ArchReg arch)
                   , MapF.ShowF (ArchReg arch)
                   , RegisterInfo (ArchReg arch)
                   )
                => IndexBounds (ArchReg arch) ids
                   -- ^ Index bounds at end of this state.
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitialIndexBounds (ArchReg arch)
nextBlockBounds bnds regs =
  let m = regStateMap regs
      nextBounds = MapF.mapMaybe (eitherToMaybe . unsignedUpperBound bnds) m
   in InitialIndexBounds { initialRegUpperBound = nextBounds
                         }
