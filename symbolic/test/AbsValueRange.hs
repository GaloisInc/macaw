{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module AbsValueRange (tests) where

import           Data.Bits ((.&.))
import qualified Data.BitVector.Sized as BV
import qualified Data.Set as Set

import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.AbsDomain.StridedInterval as MASI
import           Data.Macaw.Symbolic.Internal (absValueToBVRange)
import           Data.Macaw.Types (BVType)
import           Data.Parameterized.NatRepr
                   ( NatRepr, natValue, someNat
                   , LeqProof(..), isPosNat, testLeq, addNat, knownNat
                   )
import           Data.Parameterized.Some (Some(..))

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.Hedgehog (testPropertyNamed)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | An abstract value at some 'BVType n' (pointer width 64) together
-- with a concrete integer that belongs to the abstract set, and the
-- 'NatRepr n' needed to call 'absValueToBVRange'.
data AbsValWithConcrete where
  AbsValWithConcrete ::
    NatRepr n ->
    MA.AbsValue 64 (BVType n) ->
    Integer ->
    AbsValWithConcrete

instance Show AbsValWithConcrete where
  show (AbsValWithConcrete w av v) =
    show (MA.ppAbsValue av) ++ " contains " ++ show v
      ++ " (width " ++ show (natValue w) ++ ")"

------------------------------------------------------------------------
-- Sub-generators
------------------------------------------------------------------------

-- | Generate a FinSet abstract value at width @n@ with a concrete member.
genFinSet :: NatRepr n -> H.Gen AbsValWithConcrete
genFinSet w = do
  let maxVal = 2 ^ natValue w - 1 :: Integer
  vals <- Gen.list (Range.linear 1 8)
            (Gen.integral (Range.linear 0 maxVal))
  let s = Set.fromList vals
  v <- Gen.element (Set.toList s)
  pure (AbsValWithConcrete w (MA.FinSet s) v)

-- | Generate a StridedInterval abstract value at width @n@ with a concrete member.
genStridedInterval :: NatRepr n -> H.Gen AbsValWithConcrete
genStridedInterval w = do
  let maxVal = 2 ^ natValue w - 1 :: Integer
  b      <- Gen.integral (Range.linear 0 (maxVal - 1))
  stride <- Gen.integral (Range.linear 1 (maxVal - b))
  let maxSteps = (maxVal - b) `div` stride
  numSteps <- Gen.integral (Range.linear 0 maxSteps)
  let si = MASI.StridedInterval
             { MASI.typ    = w
             , MASI.base   = b
             , MASI.range  = numSteps
             , MASI.stride = stride
             }
  step <- Gen.integral (Range.linear 0 numSteps)
  pure (AbsValWithConcrete w (MA.StridedInterval si) (b + step * stride))

genSubValue :: NatRepr n -> H.Gen AbsValWithConcrete
genSubValue w = do
  let maxVal = 2 ^ natValue w - 1 :: Integer
  n'raw <- Gen.integral (Range.linear 1 (natValue w - 1))
  case someNat n'raw of
    Just (Some innerW)
      | Just LeqProof <- isPosNat innerW
      , Just LeqProof <- testLeq (addNat innerW (knownNat @1)) w -> do
          AbsValWithConcrete innerW' innerAv innerV <- genAbsValWithConcreteAt innerW
          case testLeq (addNat innerW' (knownNat @1)) w of
            Just LeqProof -> do
              upperBits <- Gen.integral
                             (Range.linear 0 (maxVal `div` (2 ^ natValue innerW')))
              let v = upperBits * 2 ^ natValue innerW' + innerV
              pure (AbsValWithConcrete w (MA.SubValue innerW' innerAv) v)
            Nothing -> Gen.discard
    _ -> Gen.discard

-- | Generate an abstract value at a given width together with a concrete member.
genAbsValWithConcreteAt :: NatRepr n -> H.Gen AbsValWithConcrete
genAbsValWithConcreteAt w = Gen.choice $
  [ genFinSet w
  , genStridedInterval w
  ]
  -- SubValue requires at least 2 bits (needs a strictly smaller inner width).
  ++ [ genSubValue w | natValue w >= 2 ]

-- | Generate a BV width in [1, 64] then an abstract value at that width.
genAbsValWithConcrete :: H.Gen AbsValWithConcrete
genAbsValWithConcrete = do
  nraw <- Gen.integral (Range.linear (1 :: Integer) 64)
  case someNat nraw of
    Just (Some w) | Just LeqProof <- isPosNat w -> genAbsValWithConcreteAt w
    _ -> Gen.discard

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

-- | Membership check matching 'MA.mayBeMember' for the forms we generate.
isMember :: Integer -> MA.AbsValue 64 (BVType n) -> Bool
isMember v = \case
  MA.FinSet s -> Set.member v s
  MA.StridedInterval si -> MASI.member v si
  MA.SubValue n' inner -> isMember (v .&. (2 ^ natValue n' - 1)) inner
  _ -> True

-- | Verify that 'genAbsValWithConcrete' really produces concrete values
-- that belong to the abstract set it pairs them with.
prop_generatorProducesMember :: H.Property
prop_generatorProducesMember =
  H.withTests 10000 $ H.property $ do
    AbsValWithConcrete _ av v <- H.forAll genAbsValWithConcrete
    H.assert (isMember v av)

-- | Soundness: every concrete value drawn from an 'MA.AbsValue' must lie
-- within the interval returned by 'absValueToBVRange'.
prop_absValueToBVRangeSound :: H.Property
prop_absValueToBVRangeSound =
  H.withTests 10000 $ H.property $ do
    AbsValWithConcrete w av concreteVal <- H.forAll genAbsValWithConcrete
    case absValueToBVRange w av of
      Nothing -> H.discard
      Just (lo, hi) -> do
        H.footnote $ "range: [" ++ show (BV.asUnsigned lo) ++ ", " ++ show (BV.asUnsigned hi) ++ "]"
        H.footnote $ "concrete value: " ++ show concreteVal
        let concreteValBV = BV.mkBV w concreteVal
        H.assert (lo `BV.ule` concreteValBV && concreteValBV `BV.ule` hi)

------------------------------------------------------------------------
-- Test tree
------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "absValueToBVRange"
  [ testPropertyNamed
      "genAbsValWithConcrete produces genuine members"
      "prop_generatorProducesMember"
      prop_generatorProducesMember
  , testPropertyNamed
      "range covers every concrete value in the abstract set"
      "prop_absValueToBVRangeSound"
      prop_absValueToBVRangeSound
  ]
