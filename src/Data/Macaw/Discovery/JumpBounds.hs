{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Macaw.Discovery.JumpBounds
  ( InitialIndexBounds
  , arbitraryInitialBounds
  , joinInitialBounds
  , IndexBounds
  , mkIndexBounds
  , addUpperBounds
  , lookupUpperBound
  , nextBlockBounds
  ) where

import           Control.Lens
import           Control.Monad.State
import           Data.Functor
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr (maxUnsigned)

import           Data.Macaw.CFG
import           Data.Macaw.Types

-- | An upper bound on a value.
data UpperBounds tp = forall w . (tp ~ BVType w) => IntegerUpperBound Integer

instance Eq (UpperBounds tp) where
  IntegerUpperBound x == IntegerUpperBound y = x == y

instance MapF.EqF UpperBounds where
  eqF = (==)

instance Ord (UpperBounds tp) where
  compare (IntegerUpperBound x) (IntegerUpperBound y) = compare x y

-- | Bounds for a function as the start of a block.
data InitialIndexBounds r
   = InitialIndexBounds { initialRegUpperBounds :: !(MapF r UpperBounds)
                        }

instance MapF.TestEquality r => Eq (InitialIndexBounds r) where
   x == y = initialRegUpperBounds x == initialRegUpperBounds y

-- | Create initial index bounds that can represent any system state.
arbitraryInitialBounds :: InitialIndexBounds reg
arbitraryInitialBounds = InitialIndexBounds { initialRegUpperBounds = MapF.empty }


type Changed = State Bool

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
  let combineF :: r tp -> UpperBounds tp -> UpperBounds tp -> Changed (Maybe (UpperBounds tp))
      combineF _ (IntegerUpperBound x) (IntegerUpperBound y) =
        markChanged (x < y) $> Just (IntegerUpperBound (max x y))

      -- Mark upper bounds exclusively in old set.
      -- If we have any only-old bounds add mark value as changed.
      oldF :: MapF r UpperBounds -> Changed (MapF r UpperBounds)
      oldF m = markChanged (not (MapF.null m)) $> MapF.empty

      -- How to upper bounds exclusively in new set.
      -- Drop any only-new bounds.
      newF :: MapF r UpperBounds -> Changed (MapF r UpperBounds)
      newF _ = pure MapF.empty

  z <- MapF.mergeWithKeyM combineF oldF newF (initialRegUpperBounds old) (initialRegUpperBounds new)
  pure InitialIndexBounds { initialRegUpperBounds = z }

-- | Information about bounds for a particular value within a block.
data IndexBounds reg ids
   = IndexBounds { _regBounds :: !(MapF reg UpperBounds)
                 , _assignUpperBounds :: !(MapF (AssignId ids) UpperBounds)
                 }

-- | Maps assignment ids to the associated upper bounds
regBounds :: Simple Lens (IndexBounds reg ids) (MapF reg UpperBounds)
regBounds = lens _regBounds (\s v -> s { _regBounds = v })

-- | Maps assignment ids to the associated upper bounds
assignUpperBounds :: Simple Lens (IndexBounds reg ids) (MapF (AssignId ids) UpperBounds)
assignUpperBounds = lens _assignUpperBounds (\s v -> s { _assignUpperBounds = v })

-- | Create index bounds from initial index bounds.
mkIndexBounds :: InitialIndexBounds reg -> IndexBounds reg ids
mkIndexBounds i = IndexBounds { _regBounds = initialRegUpperBounds i
                              , _assignUpperBounds = MapF.empty
                              }

addUpperBounds :: ( MapF.OrdF (ArchReg arch)
                  , HasRepr (ArchReg arch) TypeRepr
                  )
               => BVValue arch ids w
               -> Integer -- ^ Upper bound as an unsigned number
               -> IndexBounds (ArchReg arch) ids
               -> Either String (IndexBounds (ArchReg arch) ids)
addUpperBounds v u bnds
    -- Do nothing if upper bounds equals or exceeds function
  | u >= maxUnsigned (valueWidth v) = Right bnds
  | u < 0 = error "addUpperBounds given negative value."
  | otherwise =
  case v of
    BVValue _ c | c <= u -> Right bnds
                | otherwise -> Left "Constant given upper bound that is statically less than given bounds"
    RelocatableValue{} -> Left "Relocatable value does not have upper bounds."
    AssignedValue a ->
      Right $ bnds & assignUpperBounds %~ MapF.insertWith min (assignId a) (IntegerUpperBound u)
    Initial r ->
      Right $ bnds & regBounds %~ MapF.insertWith min r (IntegerUpperBound u)

lookupUpperBound :: ( MapF.OrdF (ArchReg arch)
                    , Show (ArchReg arch (BVType w))
                    )
                 => BVValue arch ids w
                 -> IndexBounds (ArchReg arch) ids
                 -> Either String Integer
lookupUpperBound v bnds =
  case v of
    BVValue _ i -> Right i
    RelocatableValue{} -> Left "Relocatable values do not have bounds."
    AssignedValue a ->
      case MapF.lookup (assignId a) (bnds^.assignUpperBounds) of
        Just (IntegerUpperBound bnd) -> Right bnd
        Nothing -> Left $ "Could not find upper bounds for " ++ show (assignId a) ++ "."
    Initial r ->
      case MapF.lookup r (bnds^.regBounds) of
        Just (IntegerUpperBound bnd) -> Right bnd
        Nothing -> Left $ "Could not find upper bounds for " ++ show r ++ "."

nextBlockBounds :: RegState r (Value arch ids)
                -> IndexBounds (ArchReg arch) ids
                -> InitialIndexBounds (ArchReg arch)
nextBlockBounds _regs _bnds =
  let m = undefined
   in InitialIndexBounds { initialRegUpperBounds = m
                         }
