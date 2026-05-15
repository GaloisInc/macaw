{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module AbsDomain.FinSetTests
  ( tests
  ) where

import           Data.Bits ((.&.), (.|.), xor)
import qualified Data.Set as Set
import           Data.Parameterized.NatRepr
import qualified Hedgehog as H
import qualified Hedgehog.Gen as H.Gen
import qualified Hedgehog.Range as H.Range
import qualified Test.Tasty as TT
import qualified Test.Tasty.Hedgehog as TTH

import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.AbsState.Internal as Ops
import           Data.Macaw.Types
import qualified AbsDomain.Gen as Gen

-- ---------------------------------------------------------------------------
-- Properties

prop_member :: H.Property
prop_member = H.property $ do
  FinSet s <- H.forAll Gen.genFinSetNonEmpty
  v <- H.forAll (H.Gen.element (Set.toList s))
  H.assert (Ops.mayBeMember v (FinSet s :: AbsValue Gen.W (BVType Gen.W)))

prop_lub_contains_operands :: H.Property
prop_lub_contains_operands = H.property $ do
  FinSet s1 <- H.forAll Gen.genFinSet
  FinSet s2 <- H.forAll Gen.genFinSet
  let u = lub (FinSet s1 :: AbsValue Gen.W (BVType Gen.W)) (FinSet s2)
  mapM_ (\v -> H.assert (Ops.mayBeMember v u)) (Set.toList s1)
  mapM_ (\v -> H.assert (Ops.mayBeMember v u)) (Set.toList s2)

prop_lub_idempotent :: H.Property
prop_lub_idempotent = H.property $ do
  x <- H.forAll Gen.genFinSet
  lub x x H.=== (x :: AbsValue Gen.W (BVType Gen.W))

prop_meet_is_intersection :: H.Property
prop_meet_is_intersection = H.property $ do
  shared  <- H.forAll Gen.genBV
  extras1 <- H.forAll (H.Gen.list (H.Range.linear 0 4) Gen.genBV)
  extras2 <- H.forAll (H.Gen.list (H.Range.linear 0 4) Gen.genBV)
  let s1 = Set.fromList (shared : extras1)
      s2 = Set.fromList (shared : extras2)
  case meet (FinSet s1 :: AbsValue Gen.W (BVType Gen.W)) (FinSet s2) of
    FinSet ms -> ms H.=== Set.intersection s1 s2
    _         -> H.failure

prop_meet_contains_shared :: H.Property
prop_meet_contains_shared = H.property $ do
  shared  <- H.forAll Gen.genBV
  extras1 <- H.forAll (H.Gen.list (H.Range.linear 0 4) Gen.genBV)
  extras2 <- H.forAll (H.Gen.list (H.Range.linear 0 4) Gen.genBV)
  let s1 = Set.fromList (shared : extras1)
      s2 = Set.fromList (shared : extras2)
  H.assert (Ops.mayBeMember shared (meet (FinSet s1 :: AbsValue Gen.W (BVType Gen.W)) (FinSet s2)))

prop_meet_idempotent :: H.Property
prop_meet_idempotent = H.property $ do
  x <- H.forAll Gen.genFinSet
  meet x x H.=== (x :: AbsValue Gen.W (BVType Gen.W))

prop_leq_reflexive :: H.Property
prop_leq_reflexive = H.property $ do
  x <- H.forAll Gen.genFinSet
  H.assert (leq x (x :: AbsValue Gen.W (BVType Gen.W)))

prop_leq_antisymmetric :: H.Property
prop_leq_antisymmetric = H.property $ do
  vs    <- H.forAll (H.Gen.list (H.Range.exponential 1 256) Gen.genBV)
  extra <- H.forAll Gen.genBV
  let sub = Set.fromList vs
      sup = Set.insert extra sub
      x   = FinSet sub :: AbsValue Gen.W (BVType Gen.W)
      y   = FinSet sup
  H.assert (leq x y)
  if sub == sup
    then H.assert (leq y x)
    else H.assert (not (leq y x))

-- ---------------------------------------------------------------------------
-- Arithmetic soundness

prop_bvadd_sound :: H.Property
prop_bvadd_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (bv, y) <- H.forAll Gen.genFinSetNonEmptyWithElement
  H.assert (Ops.mayBeMember ((x + y) `mod` Gen.modulus64) (Ops.bvadd Gen.w av bv))

prop_bvadc_sound :: H.Property
prop_bvadc_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (bv, y) <- H.forAll Gen.genFinSetNonEmptyWithElement
  carry   <- H.forAll H.Gen.bool
  H.assert (Ops.mayBeMember ((x + y + if carry then 1 else 0) `mod` Gen.modulus64)
                             (Ops.bvadc Gen.w av bv (BoolConst carry)))

prop_bvinc_sound :: H.Property
prop_bvinc_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  o <- H.forAll Gen.genBV
  H.assert (Ops.mayBeMember ((x + o) `mod` Gen.modulus64) (Ops.bvinc Gen.w av o))

prop_bvmul_sound :: H.Property
prop_bvmul_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (bv, y) <- H.forAll Gen.genFinSetNonEmptyWithElement
  H.assert (Ops.mayBeMember ((x * y) `mod` Gen.modulus64) (Ops.bvmul Gen.w av bv))

prop_bvsub_sound :: H.Property
prop_bvsub_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (bv, y) <- H.forAll Gen.genFinSetNonEmptyWithElement
  H.assert (Ops.mayBeMember ((x - y) `mod` Gen.modulus64) (Ops.bvsub Gen.mem64 Gen.w av bv))

prop_bvsbb_sound :: H.Property
prop_bvsbb_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (bv, y) <- H.forAll Gen.genFinSetNonEmptyWithElement
  borrow  <- H.forAll H.Gen.bool
  H.assert (Ops.mayBeMember ((x - y - if borrow then 1 else 0) `mod` Gen.modulus64)
                             (Ops.bvsbb Gen.mem64 Gen.w av bv (BoolConst borrow)))

prop_trunc_sound :: H.Property
prop_trunc_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  H.assert (Ops.mayBeMember (x `mod` Gen.modulus32)
                             (Ops.trunc av (knownNat :: NatRepr 32)))

prop_uext_sound :: H.Property
prop_uext_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement32
  H.assert (Ops.mayBeMember x (Ops.uext av Gen.w))

prop_bitop_and_sound :: H.Property
prop_bitop_and_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (bv, y) <- H.forAll Gen.genFinSetNonEmptyWithElement
  H.assert (Ops.mayBeMember (x .&. y) (Ops.bitop (.&.) Gen.w av bv))

prop_bitop_or_sound :: H.Property
prop_bitop_or_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (bv, y) <- H.forAll Gen.genFinSetNonEmptyWithElement
  H.assert (Ops.mayBeMember (x .|. y) (Ops.bitop (.|.) Gen.w av bv))

prop_bitop_xor_sound :: H.Property
prop_bitop_xor_sound = H.property $ do
  (av, x) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (bv, y) <- H.forAll Gen.genFinSetNonEmptyWithElement
  H.assert (Ops.mayBeMember (x `xor` y) (Ops.bitop xor Gen.w av bv))

-- ---------------------------------------------------------------------------
-- abstractULt / abstractULeq (refinement under unsigned comparison)
--
-- Restricted to FinSet inputs: 'meet' over StridedInterval relies on
-- 'SI.glb', which can drop concrete witnesses that satisfy the comparison
-- (its result is a strided interval that under-approximates the true
-- intersection). On FinSet inputs 'meet' is exact via 'Set.intersection'.

prop_abstractULt_sound :: H.Property
prop_abstractULt_sound = H.property $ do
  (p, a) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (q, b) <- H.forAll Gen.genFinSetNonEmptyWithElement
  if a == b
    then H.discard
    else do
      let ((x, a'), (y, b')) | a < b     = ((p, a), (q, b))
                             | otherwise = ((q, b), (p, a))
          (x', y') = abstractULt Gen.w x y
      H.assert (Ops.mayBeMember a' x')
      H.assert (Ops.mayBeMember b' y')

prop_abstractULt_lower_bound :: H.Property
prop_abstractULt_lower_bound = H.property $ do
  x <- H.forAll Gen.genFinSetNonEmpty
  y <- H.forAll Gen.genFinSetNonEmpty
  let (x', y') = abstractULt Gen.w x y
  H.assert (leq x' x)
  H.assert (leq y' y)

prop_abstractULeq_sound :: H.Property
prop_abstractULeq_sound = H.property $ do
  (p, a) <- H.forAll Gen.genFinSetNonEmptyWithElement
  (q, b) <- H.forAll Gen.genFinSetNonEmptyWithElement
  let ((x, a'), (y, b')) | a <= b    = ((p, a), (q, b))
                         | otherwise = ((q, b), (p, a))
      (x', y') = abstractULeq Gen.w x y
  H.assert (Ops.mayBeMember a' x')
  H.assert (Ops.mayBeMember b' y')

prop_abstractULeq_lower_bound :: H.Property
prop_abstractULeq_lower_bound = H.property $ do
  x <- H.forAll Gen.genFinSetNonEmpty
  y <- H.forAll Gen.genFinSetNonEmpty
  let (x', y') = abstractULeq Gen.w x y
  H.assert (leq x' x)
  H.assert (leq y' y)

-- ---------------------------------------------------------------------------
-- Test tree

tests :: TT.TestTree
tests = TT.testGroup "FinSet"
  [ TTH.testProperty "elements satisfy mayBeMember" prop_member
  , TTH.testProperty "lub contains both operands" prop_lub_contains_operands
  , TTH.testProperty "lub idempotent" prop_lub_idempotent
  , TTH.testProperty "meet is set intersection" prop_meet_is_intersection
  , TTH.testProperty "meet contains shared element" prop_meet_contains_shared
  , TTH.testProperty "meet idempotent" prop_meet_idempotent
  , TTH.testProperty "leq reflexive" prop_leq_reflexive
  , TTH.testProperty "leq antisymmetric" prop_leq_antisymmetric
  , TTH.testProperty "bvadd sound" prop_bvadd_sound
  , TTH.testProperty "bvadc sound" prop_bvadc_sound
  , TTH.testProperty "bvinc sound" prop_bvinc_sound
  , TTH.testProperty "bvmul sound" prop_bvmul_sound
  , TTH.testProperty "bvsub sound" prop_bvsub_sound
  , TTH.testProperty "bvsbb sound" prop_bvsbb_sound
  , TTH.testProperty "trunc sound" prop_trunc_sound
  , TTH.testProperty "uext sound" prop_uext_sound
  , TTH.testProperty "bitop AND sound" prop_bitop_and_sound
  , TTH.testProperty "bitop OR sound" prop_bitop_or_sound
  , TTH.testProperty "bitop XOR sound" prop_bitop_xor_sound
  , TTH.testProperty "abstractULt sound (preserves witnesses)" prop_abstractULt_sound
  , TTH.testProperty "abstractULt refines (output <= input)" prop_abstractULt_lower_bound
  , TTH.testProperty "abstractULeq sound (preserves witnesses)" prop_abstractULeq_sound
  , TTH.testProperty "abstractULeq refines (output <= input)" prop_abstractULeq_lower_bound
  ]
