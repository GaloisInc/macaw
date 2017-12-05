{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.TypedList
  ( TList(..)
  , Index(..)
  , indexValue
  , (!)
  , index0
  , index1
  , index2
  ) where

import Data.Parameterized.Classes
import Data.Parameterized.TraversableFC

data TList (f :: k -> *) (ctx :: [k]) where
  (:|)  :: f tp -> TList f ctx -> TList f (tp:ctx)
  Empty :: TList f '[]

instance FunctorFC TList where
  fmapFC = fmapFCDefault

instance FoldableFC TList where
  foldMapFC = foldMapFCDefault

instance TraversableFC TList where
  traverseFC _ Empty = pure Empty
  traverseFC f (h :| r) = (:|) <$> f h <*> traverseFC f r

instance TestEquality f => TestEquality (TList f) where
  testEquality Empty Empty = Just Refl
  testEquality (xh :| xl) (yh :| yl) = do
    Refl <- testEquality xh yh
    Refl <- testEquality xl yl
    pure Refl
  testEquality _ _ = Nothing

instance OrdF f => OrdF (TList f) where
  compareF Empty Empty = EQF
  compareF Empty _ = LTF
  compareF _ Empty = GTF
  compareF (xh :| xl) (yh :| yl) =
    lexCompareF xh yh $
    lexCompareF xl yl $
    EQF

-- | An index into a list of types.
data Index (l :: [k]) (tp :: k) where
  ZeroIndex :: Index (x:r) x
  ConsIndex :: !(Index r y) -> Index (x:r) y

(!) :: TList (f :: k -> *) (l :: [k]) -> Index l (x :: k) -> f x
l ! ConsIndex i =
  case l of
    _ :| r -> r ! i
l ! ZeroIndex =
  case l of
    (h :| _) -> h

instance TestEquality (Index l) where
  testEquality ZeroIndex ZeroIndex = Just Refl
  testEquality (ConsIndex x) (ConsIndex y) = (\Refl -> Refl) <$> testEquality x y
  testEquality _ _ = Nothing

instance OrdF (Index l) where
  compareF ZeroIndex ZeroIndex = EQF
  compareF ZeroIndex _ = LTF
  compareF _ ZeroIndex = GTF
  compareF (ConsIndex x) (ConsIndex y) = compareF x y

indexValue :: Index l x -> Integer
indexValue = go 0
  where go :: Integer -> Index l x -> Integer
        go i ZeroIndex = i
        go i (ConsIndex x) = go (i+1) x

index0 :: Index (x:r) x
index0 = ZeroIndex

index1 :: Index (x0:x1:r) x1
index1 = ConsIndex index0

index2 :: Index (x0:x1:x2:r) x2
index2 = ConsIndex index1
