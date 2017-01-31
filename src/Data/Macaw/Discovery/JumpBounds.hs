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
  , addUpperBound
  , lookupUpperBound
  , nextBlockBounds
  ) where

import           Control.Lens
import           Control.Monad.State
import           Data.Functor
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr (maxUnsigned)

import           Data.Macaw.CFG
import           Data.Macaw.Types

-- | An upper bound on a value.
data UpperBound tp = forall w . (tp ~ BVType w) => IntegerUpperBound Integer

instance Eq (UpperBound tp) where
  IntegerUpperBound x == IntegerUpperBound y = x == y

instance MapF.EqF UpperBound where
  eqF = (==)

instance Ord (UpperBound tp) where
  compare (IntegerUpperBound x) (IntegerUpperBound y) = compare x y

-- | Bounds for a function as the start of a block.
data InitialIndexBounds r
   = InitialIndexBounds { initialRegUpperBound :: !(MapF r UpperBound)
                        }

instance MapF.TestEquality r => Eq (InitialIndexBounds r) where
   x == y = initialRegUpperBound x == initialRegUpperBound y

-- | Create initial index bounds that can represent any system state.
arbitraryInitialBounds :: InitialIndexBounds reg
arbitraryInitialBounds = InitialIndexBounds { initialRegUpperBound = MapF.empty }


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
  let combineF :: r tp -> UpperBound tp -> UpperBound tp -> Changed (Maybe (UpperBound tp))
      combineF _ (IntegerUpperBound x) (IntegerUpperBound y) =
        markChanged (x < y) $> Just (IntegerUpperBound (max x y))

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

addUpperBound :: ( MapF.OrdF (ArchReg arch)
                  , HasRepr (ArchReg arch) TypeRepr
                  )
               => BVValue arch ids w
               -> Integer -- ^ Upper bound as an unsigned number
               -> IndexBounds (ArchReg arch) ids
               -> Either String (IndexBounds (ArchReg arch) ids)
addUpperBound v u bnds
    -- Do nothing if upper bounds equals or exceeds function
  | u >= maxUnsigned (valueWidth v) = Right bnds
  | u < 0 = error "addUpperBound given negative value."
  | otherwise =
  case v of
    BVValue _ c | c <= u -> Right bnds
                | otherwise -> Left "Constant given upper bound that is statically less than given bounds"
    RelocatableValue{} -> Left "Relocatable value does not have upper bounds."
    AssignedValue a ->
      Right $ bnds & assignUpperBound %~ MapF.insertWith min (assignId a) (IntegerUpperBound u)
    Initial r ->
      Right $ bnds & regBounds %~ MapF.insertWith min r (IntegerUpperBound u)

-- | Lookup an upper bound or return analysis for why it is not defined.
lookupUpperBound :: ( MapF.OrdF (ArchReg arch)
                    , MapF.ShowF (ArchReg arch)
                    )
                  => IndexBounds (ArchReg arch) ids
                  -> Value arch ids tp
                  -> Either String (UpperBound tp)
lookupUpperBound bnds v =
  case v of
    BVValue _ i -> Right (IntegerUpperBound i)
    RelocatableValue{} ->
      Left "Relocatable values do not have bounds."
    AssignedValue a ->
      case MapF.lookup (assignId a) (bnds^.assignUpperBound) of
        Just bnd -> Right bnd
        Nothing -> Left $ "Could not find upper bounds for " ++ show (assignId a) ++ "."
    Initial r ->
      case MapF.lookup r (bnds^.regBounds) of
        Just bnd -> Right bnd
        Nothing -> Left $ "Could not find upper bounds for " ++ showF r ++ "."


eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe (Right v) = Just v
eitherToMaybe Left{}    = Nothing


nextBlockBounds :: forall arch ids
                .  ( MapF.OrdF (ArchReg arch)
                   , MapF.ShowF (ArchReg arch)
                   )
                => IndexBounds (ArchReg arch) ids
                   -- ^ Index bounds at end of this state.
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitialIndexBounds (ArchReg arch)
nextBlockBounds bnds regs =
  let m = regStateMap regs
      nextBounds = MapF.mapMaybe (eitherToMaybe . lookupUpperBound bnds) m
   in InitialIndexBounds { initialRegUpperBound = nextBounds
                         }
