{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module AbsDomain.StridedIntervalTests
  ( tests
  ) where

import           Data.Parameterized.NatRepr
import qualified Hedgehog as H
import qualified Hedgehog.Gen as H.Gen
import qualified Test.Tasty as TT
import qualified Test.Tasty.Hedgehog as TTH

import           Data.Macaw.AbsDomain.StridedInterval
import qualified AbsDomain.Gen as Gen

-- ---------------------------------------------------------------------------
-- Properties

prop_toList_member :: H.Property
prop_toList_member = H.property $ do
  si <- H.forAll Gen.genSI
  mapM_ (\x -> H.assert (member x si)) (toList si)

prop_member_toList :: H.Property
prop_member_toList = H.property $ do
  si <- H.forAll Gen.genNonEmpty
  x  <- H.forAll (Gen.genElement si)
  H.assert (member x si)

prop_isSingleton_consistent :: H.Property
prop_isSingleton_consistent = H.property $ do
  si <- H.forAll Gen.genSI
  case isSingleton si of
    Just v  -> toList si H.=== [v]
    Nothing -> pure ()

prop_lub_idempotent :: H.Property
prop_lub_idempotent = H.property $ do
  si <- H.forAll Gen.genSI
  lub si si H.=== si

prop_lub_commutative :: H.Property
prop_lub_commutative = H.property $ do
  a <- H.forAll Gen.genSI
  b <- H.forAll Gen.genSI
  mapM_ (\x -> H.assert (member x (lub b a))) (toList a)
  mapM_ (\x -> H.assert (member x (lub b a))) (toList b)
  mapM_ (\x -> H.assert (member x (lub a b))) (toList a)
  mapM_ (\x -> H.assert (member x (lub a b))) (toList b)

prop_lub_contains_operands :: H.Property
prop_lub_contains_operands = H.property $ do
  a <- H.forAll Gen.genSI
  b <- H.forAll Gen.genSI
  H.assert (isSubsetOf a (lub a b))
  H.assert (isSubsetOf b (lub a b))

prop_glb_subset :: H.Property
prop_glb_subset = H.property $ do
  a <- H.forAll Gen.genSI
  b <- H.forAll Gen.genSI
  let g = glb a b
  case toList g of
    [] -> pure ()
    xs -> do
      x <- H.forAll (H.Gen.element xs)
      H.assert (member x a)
      H.assert (member x b)

prop_glb_completeness_singletons :: H.Property
prop_glb_completeness_singletons = H.property $ do
  b <- H.forAll Gen.genNonEmpty
  x <- H.forAll (Gen.genElement b)
  let a = singleton Gen.w x
  H.assert (member x a)
  H.assert (member x b)
  H.assert (member x (glb a b))

prop_isSubsetOf_sound :: H.Property
prop_isSubsetOf_sound = H.property $ do
  a <- H.forAll Gen.genSI
  c <- H.forAll Gen.genSI
  let b = lub a c
  H.assert (isSubsetOf a b)
  mapM_ (\x -> H.assert (member x b)) (toList a)

prop_isSubsetOf_reflexive :: H.Property
prop_isSubsetOf_reflexive = H.property $ do
  si <- H.forAll Gen.genSI
  H.assert (isSubsetOf si si)

-- ---------------------------------------------------------------------------
-- Arithmetic soundness

prop_bvadd_sound :: H.Property
prop_bvadd_sound = H.property $ do
  a <- H.forAll Gen.genNonEmpty
  b <- H.forAll Gen.genNonEmpty
  x <- H.forAll (Gen.genElement a)
  y <- H.forAll (Gen.genElement b)
  H.assert (member ((x + y) `mod` Gen.modulus64) (bvadd Gen.w a b))

prop_bvadc_sound :: H.Property
prop_bvadc_sound = H.property $ do
  a     <- H.forAll Gen.genNonEmpty
  b     <- H.forAll Gen.genNonEmpty
  x     <- H.forAll (Gen.genElement a)
  y     <- H.forAll (Gen.genElement b)
  carry <- H.forAll H.Gen.bool
  H.assert (member ((x + y + if carry then 1 else 0) `mod` Gen.modulus64)
                   (bvadc Gen.w a b (Just carry)))

prop_bvmul_sound :: H.Property
prop_bvmul_sound = H.property $ do
  a <- H.forAll Gen.genNonEmpty
  b <- H.forAll Gen.genNonEmpty
  x <- H.forAll (Gen.genElement a)
  y <- H.forAll (Gen.genElement b)
  H.assert (member ((x * y) `mod` Gen.modulus64) (bvmul Gen.w a b))

prop_trunc_sound :: H.Property
prop_trunc_sound = H.property $ do
  si <- H.forAll Gen.genNonEmpty
  x  <- H.forAll (Gen.genElement si)
  H.assert (member (x `mod` Gen.modulus32) (trunc si (knownNat :: NatRepr 32)))

-- ---------------------------------------------------------------------------
-- Test tree

tests :: TT.TestTree
tests = TT.testGroup "StridedInterval"
  [ TTH.testProperty "toList elements satisfy member" prop_toList_member
  , TTH.testProperty "member implies element in toList" prop_member_toList
  , TTH.testProperty "isSingleton consistent with toList" prop_isSingleton_consistent
  , TTH.testProperty "lub idempotent" prop_lub_idempotent
  , TTH.testProperty "lub commutative (membership)" prop_lub_commutative
  , TTH.testProperty "lub contains both operands" prop_lub_contains_operands
  , TTH.testProperty "glb subset of both operands" prop_glb_subset
  , TTH.testProperty "glb completeness on singletons" prop_glb_completeness_singletons
  , TTH.testProperty "isSubsetOf sound" prop_isSubsetOf_sound
  , TTH.testProperty "isSubsetOf reflexive" prop_isSubsetOf_reflexive
  , TTH.testProperty "bvadd sound" prop_bvadd_sound
  , TTH.testProperty "bvadc sound" prop_bvadc_sound
  , TTH.testProperty "bvmul sound" prop_bvmul_sound
  , TTH.testProperty "trunc sound" prop_trunc_sound
  ]
