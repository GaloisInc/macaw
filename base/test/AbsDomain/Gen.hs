{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Generators and generator membership tests for abstract-domain types.
module AbsDomain.Gen
  ( -- * Width
    W
  , w
    -- * Scalar
  , genBV
  , genBV32
    -- * StridedInterval
  , genSI
  , genNonEmpty
  , genElement
  , genSIValue
  , genSIValueWithElement
  , genSIValue32WithElement
    -- * FinSet
  , genFinSet
  , genFinSetNonEmpty
  , genFinSetNonEmptyWithElement
  , genFinSetNonEmptyWithElement32
    -- * Address / stack
  , genMemAddr
  , genStackOffset
  , genStackOffsetWithElement
    -- * CodePointers
  , genCodePointers
  , genCodePointersWithElement
    -- * Mixed AbsValue
  , genAbsValue
  , genAbsValueWithElement
  , genAbsValue32WithElement
  , genOverlappingPair
  , genSingleton
  , genBottom
    -- * Memory helper
  , mem64
    -- * Bit-width moduli
  , modulus64
  , modulus32
    -- * Generator membership tests
  , tests
  ) where

import           Data.Int (Int64)
import qualified Data.Set as Set
import           Data.Parameterized.NatRepr
import qualified Hedgehog as H
import qualified Hedgehog.Gen as H.Gen
import qualified Hedgehog.Range as H.Range
import qualified Test.Tasty as TT
import qualified Test.Tasty.Hedgehog as TTH

import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.AbsState.Internal as Ops
import           Data.Macaw.AbsDomain.StridedInterval (StridedInterval)
import qualified Data.Macaw.AbsDomain.StridedInterval as SI
import qualified Data.Macaw.Memory as Mem
import           Data.Macaw.Memory (MemAddr(..), memWord, RegionIndex)
import           Data.Macaw.Types

-- ---------------------------------------------------------------------------
-- Width

type W = 64

w :: NatRepr W
w = knownNat

-- ---------------------------------------------------------------------------
-- Scalar

genBV :: H.Gen Integer
genBV = H.Gen.integral (H.Range.linear 0 (maxUnsigned w))

genBV32 :: H.Gen Integer
genBV32 = H.Gen.integral (H.Range.linear 0 (maxUnsigned (knownNat :: NatRepr 32)))

-- ---------------------------------------------------------------------------
-- StridedInterval

maxSISize :: Integer
maxSISize = 2 ^ (16 :: Int)

-- | Any 'StridedInterval' at width 64, including empty and singleton.
-- Capped at 2^16 elements so properties calling 'SI.toList' stay fast.
-- All elements are guaranteed to fit in [0, maxUnsigned w].
genSI :: H.Gen (StridedInterval 64)
genSI = H.Gen.frequency
  [ (1, pure (SI.mkStridedInterval w True 0 (-1) 1))  -- empty
  , (3, SI.singleton w <$> genBV)
  , (6, do
       lo <- genBV
       -- room is maxUnsigned w - lo, so lo + (nelems-1)*s <= maxUnsigned w
       -- holds as long as (nelems-1)*s <= room.
       let room = maxUnsigned w - lo
       s      <- H.Gen.integral (H.Range.exponentialFrom 1 1 (max 1 room))
       let maxN = 1 + (room `div` max 1 s)
       nelems <- H.Gen.integral (H.Range.exponential 1 (min maxSISize maxN))
       let hi = lo + (nelems - 1) * s
       pure (SI.mkStridedInterval w True lo hi s))
  ]

genNonEmpty :: H.Gen (StridedInterval 64)
genNonEmpty = H.Gen.filter (not . null . SI.toList) genSI

genElement :: StridedInterval 64 -> H.Gen Integer
genElement si = H.Gen.element (SI.toList si)

-- | Wrap a non-empty 'StridedInterval' as an 'AbsValue'.
genSIValue :: H.Gen (AbsValue W (BVType W))
genSIValue = StridedInterval <$> genNonEmpty

-- | Non-empty 64-bit 'StridedInterval' paired with one of its elements.
genSIValueWithElement :: H.Gen (AbsValue W (BVType W), Integer)
genSIValueWithElement = do
  si <- genNonEmpty
  v  <- genElement si
  pure (StridedInterval si, v)

-- | Non-empty 32-bit 'StridedInterval' (pointer width 64) paired with one of
-- its elements.
genSIValue32WithElement :: H.Gen (AbsValue W (BVType 32), Integer)
genSIValue32WithElement = do
  vs <- H.Gen.list (H.Range.exponential 1 64) genBV32
  -- 'vs' is non-empty (range starts at 1), so 'fromFoldable' is non-empty
  -- and contains every element of 'vs'.
  let si = SI.fromFoldable (knownNat :: NatRepr 32) vs
  v <- H.Gen.element vs
  pure (StridedInterval si, v)

-- ---------------------------------------------------------------------------
-- FinSet

genFinSet :: H.Gen (AbsValue W (BVType W))
genFinSet = FinSet . Set.fromList <$> H.Gen.list (H.Range.exponential 0 256) genBV

genFinSetNonEmpty :: H.Gen (AbsValue W (BVType W))
genFinSetNonEmpty = FinSet . Set.fromList <$> H.Gen.list (H.Range.exponential 1 256) genBV

-- | Non-empty 64-bit 'FinSet' paired with one of its elements.
genFinSetNonEmptyWithElement :: H.Gen (AbsValue W (BVType W), Integer)
genFinSetNonEmptyWithElement = do
  vs <- H.Gen.list (H.Range.exponential 1 256) genBV
  let s = Set.fromList vs
  v <- H.Gen.element (Set.toList s)
  pure (FinSet s, v)

-- | Non-empty 32-bit 'FinSet' (pointer width 64) paired with one of its elements.
genFinSetNonEmptyWithElement32 :: H.Gen (AbsValue W (BVType 32), Integer)
genFinSetNonEmptyWithElement32 = do
  vs <- H.Gen.list (H.Range.exponential 1 256) genBV32
  let s = Set.fromList vs
  v <- H.Gen.element (Set.toList s)
  pure (FinSet s, v)

-- ---------------------------------------------------------------------------
-- Address / stack

genMemAddr :: H.Gen (MemAddr W)
genMemAddr = do
  reg <- H.Gen.integral (H.Range.linear 0 (maxBound :: RegionIndex))
  off <- H.Gen.word64 (H.Range.linear 0 maxBound)
  pure (MemAddr reg (memWord off))

genStackOffset :: H.Gen (AbsValue W (BVType W))
genStackOffset = do
  addr <- genMemAddr
  off  <- H.Gen.integral (H.Range.linearFrom 0 minBound maxBound) :: H.Gen Int64
  pure (StackOffsetAbsVal addr off)

-- | 'StackOffsetAbsVal' paired with any BV element (catch-all: mayBeMember = True).
genStackOffsetWithElement :: H.Gen (AbsValue W (BVType W), Integer)
genStackOffsetWithElement = (,) <$> genStackOffset <*> genBV

-- ---------------------------------------------------------------------------
-- CodePointers

-- | 'CodePointers' without live segment sets (no 'Memory' needed).
genCodePointers :: H.Gen (AbsValue W (BVType W))
genCodePointers = H.Gen.element
  [ CodePointers Set.empty False  -- bottom
  , CodePointers Set.empty True   -- {0}
  ]

-- | 'CodePointers Set.empty True' paired with 0, the only denotable element.
genCodePointersWithElement :: H.Gen (AbsValue W (BVType W), Integer)
genCodePointersWithElement = pure (CodePointers Set.empty True, 0)

-- ---------------------------------------------------------------------------
-- Mixed AbsValue

genAbsValue :: H.Gen (AbsValue W (BVType W))
genAbsValue = H.Gen.frequency
  [ (1, pure TopV)
  , (1, pure ReturnAddr)
  , (2, genCodePointers)
  , (3, genFinSet)
  , (3, genSIValue)
  , (2, genStackOffset)
  , (1, SomeStackOffset <$> genMemAddr)
  ]

-- | Any abstract value (width 64) paired with a concrete member.
genAbsValueWithElement :: H.Gen (AbsValue W (BVType W), Integer)
genAbsValueWithElement = H.Gen.frequency
  [ (3, genFinSetNonEmptyWithElement)
  , (3, genSIValueWithElement)
  , (2, genStackOffsetWithElement)
  , (1, genCodePointersWithElement)
  ]

-- | Any 32-bit abstract value paired with a concrete member (for uext tests).
genAbsValue32WithElement :: H.Gen (AbsValue W (BVType 32), Integer)
genAbsValue32WithElement = H.Gen.frequency
  [ (1, genFinSetNonEmptyWithElement32)
  , (1, genSIValue32WithElement)
  ]

-- | A pair of abstract values sharing at least one element. One side is
-- always a 'FinSet' (so the meet collapses to a 'FinSet'); the other side
-- is a non-empty FinSet or StridedInterval. Either side may be the FinSet
-- to exercise both argument orders of @meet@.
genOverlappingPair :: H.Gen (AbsValue W (BVType W), AbsValue W (BVType W))
genOverlappingPair = do
  (other, v) <- H.Gen.frequency
    [ (1, genFinSetNonEmptyWithElement)
    , (1, genSIValueWithElement)
    ]
  extras <- H.Gen.list (H.Range.linear 0 4) genBV
  let fs = FinSet (Set.fromList (v : extras))
  H.Gen.element [(other, fs), (fs, other)]

genSingleton :: H.Gen (AbsValue W (BVType W))
genSingleton = H.Gen.frequency
  [ (3, FinSet . Set.singleton <$> genBV)
  , (2, StridedInterval . SI.singleton w <$> genBV)
  ]

genBottom :: H.Gen (AbsValue W (BVType W))
genBottom = H.Gen.frequency
  [ (2, pure (FinSet Set.empty))
  , (2, pure (CodePointers Set.empty False))
  ]

-- ---------------------------------------------------------------------------
-- Memory helper

-- | Empty 64-bit memory: safe for all generators (no live CodePointers).
mem64 :: Mem.Memory W
mem64 = Mem.emptyMemory Mem.Addr64

-- ---------------------------------------------------------------------------
-- Bit-width moduli

modulus64 :: Integer
modulus64 = 2 ^ (64 :: Int)

modulus32 :: Integer
modulus32 = 2 ^ (32 :: Int)

-- ---------------------------------------------------------------------------
-- Generator membership tests

prop_finset_withElement_member :: H.Property
prop_finset_withElement_member = H.property $ do
  (av, v) <- H.forAll genFinSetNonEmptyWithElement
  H.assert (Ops.mayBeMember v av)

prop_si_withElement_member :: H.Property
prop_si_withElement_member = H.property $ do
  (av, v) <- H.forAll genSIValueWithElement
  H.assert (Ops.mayBeMember v av)

prop_stackOffset_withElement_member :: H.Property
prop_stackOffset_withElement_member = H.property $ do
  (av, v) <- H.forAll genStackOffsetWithElement
  H.assert (Ops.mayBeMember v av)

prop_codePointers_withElement_member :: H.Property
prop_codePointers_withElement_member = H.property $ do
  (av, v) <- H.forAll genCodePointersWithElement
  H.assert (Ops.mayBeMember v av)

prop_absValue32_withElement_member :: H.Property
prop_absValue32_withElement_member = H.property $ do
  (av, v) <- H.forAll genAbsValue32WithElement
  H.assert (Ops.mayBeMember v av)

tests :: TT.TestTree
tests = TT.testGroup "Gen"
  [ TTH.testProperty "FinSet WithElement member" prop_finset_withElement_member
  , TTH.testProperty "StridedInterval WithElement member" prop_si_withElement_member
  , TTH.testProperty "StackOffset WithElement member" prop_stackOffset_withElement_member
  , TTH.testProperty "CodePointers WithElement member" prop_codePointers_withElement_member
  , TTH.testProperty "AbsValue32 WithElement member" prop_absValue32_withElement_member
  ]
