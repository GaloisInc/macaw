{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Property tests for 'AbsValue' and the 'AbsDomain' class.
module AbsDomain.AbsValueTests
  ( tests
  ) where

import           Data.Bits ((.&.), (.|.), xor)
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
import           Data.Macaw.Types
import qualified AbsDomain.Gen as Gen

-- ---------------------------------------------------------------------------
-- AbsDomain lattice law properties

prop_top_upperBound :: H.Property
prop_top_upperBound = H.property $ do
  x <- H.forAll Gen.genAbsValue
  H.assert (leq x (top :: AbsValue Gen.W (BVType Gen.W)))

prop_leq_reflexive :: H.Property
prop_leq_reflexive = H.property $ do
  x <- H.forAll Gen.genAbsValue
  H.assert (leq x x)

prop_lub_upper_bound :: H.Property
prop_lub_upper_bound = H.property $ do
  x <- H.forAll Gen.genAbsValue
  y <- H.forAll Gen.genAbsValue
  let u = lub x y
  H.assert (leq x u)
  H.assert (leq y u)

prop_joinD_idempotent :: H.Property
prop_joinD_idempotent = H.property $ do
  x <- H.forAll Gen.genAbsValue
  joinD x x H.=== Nothing

prop_joinD_lub_consistent :: H.Property
prop_joinD_lub_consistent = H.property $ do
  old <- H.forAll Gen.genAbsValue
  new <- H.forAll Gen.genAbsValue
  case joinD old new of
    Nothing -> leq new old H.=== True
    Just r  -> H.assert (leq old r && leq new r)

-- ---------------------------------------------------------------------------
-- meet (refinement) properties

prop_meet_lower_bound_left :: H.Property
prop_meet_lower_bound_left = H.property $ do
  (x, y) <- H.forAll Gen.genOverlappingPair
  H.assert (leq (meet x y) x)

prop_meet_lower_bound_right :: H.Property
prop_meet_lower_bound_right = H.property $ do
  (x, y) <- H.forAll Gen.genOverlappingPair
  H.assert (leq (meet x y) y)

prop_meet_sound :: H.Property
prop_meet_sound = H.property $ do
  (x, v) <- H.forAll (H.Gen.frequency
    [ (1, Gen.genFinSetNonEmptyWithElement)
    , (1, Gen.genSIValueWithElement)
    ])
  extras <- H.forAll (H.Gen.list (H.Range.linear 0 4) Gen.genBV)
  H.assert (Ops.mayBeMember v (meet x (FinSet (Set.fromList (v : extras)))))

prop_meet_commutative :: H.Property
prop_meet_commutative = H.property $ do
  (x, y) <- H.forAll Gen.genOverlappingPair
  case (meet x y, meet y x) of
    (FinSet mxy, FinSet myx) -> do
      v <- H.forAll (H.Gen.element (Set.toList mxy))
      H.assert (Set.member v myx)
    _ -> H.failure

prop_meet_idempotent :: H.Property
prop_meet_idempotent = H.property $ do
  x <- H.forAll (H.Gen.frequency
    [ (1, Gen.genFinSetNonEmpty)
    , (1, Gen.genSIValue)
    ])
  meet x x H.=== x

prop_meet_top_identity :: H.Property
prop_meet_top_identity = H.property $ do
  x <- H.forAll Gen.genAbsValue
  meet TopV x H.=== x
  meet x TopV H.=== x

-- ---------------------------------------------------------------------------
-- Arithmetic soundness (mixed shapes via genAbsValueWithElement)

prop_bvadd_sound :: H.Property
prop_bvadd_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  (bv, y) <- H.forAll Gen.genAbsValueWithElement
  H.assert (Ops.mayBeMember ((x + y) `mod` Gen.modulus64) (bvadd Gen.w av bv))

prop_bvadc_sound :: H.Property
prop_bvadc_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  (bv, y) <- H.forAll Gen.genAbsValueWithElement
  carry   <- H.forAll H.Gen.bool
  H.assert (Ops.mayBeMember ((x + y + if carry then 1 else 0) `mod` Gen.modulus64)
                             (Ops.bvadc Gen.w av bv (BoolConst carry)))

prop_bvinc_sound :: H.Property
prop_bvinc_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  o <- H.forAll Gen.genBV
  H.assert (Ops.mayBeMember ((x + o) `mod` Gen.modulus64) (Ops.bvinc Gen.w av o))

prop_bvmul_sound :: H.Property
prop_bvmul_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  (bv, y) <- H.forAll Gen.genAbsValueWithElement
  H.assert (Ops.mayBeMember ((x * y) `mod` Gen.modulus64) (Ops.bvmul Gen.w av bv))

prop_bvsub_sound :: H.Property
prop_bvsub_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  (bv, y) <- H.forAll Gen.genAbsValueWithElement
  H.assert (Ops.mayBeMember ((x - y) `mod` Gen.modulus64) (Ops.bvsub Gen.mem64 Gen.w av bv))

prop_bvsbb_sound :: H.Property
prop_bvsbb_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  (bv, y) <- H.forAll Gen.genAbsValueWithElement
  borrow  <- H.forAll H.Gen.bool
  H.assert (Ops.mayBeMember ((x - y - if borrow then 1 else 0) `mod` Gen.modulus64)
                             (Ops.bvsbb Gen.mem64 Gen.w av bv (BoolConst borrow)))

prop_trunc_sound :: H.Property
prop_trunc_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  H.assert (Ops.mayBeMember (x `mod` Gen.modulus32)
                             (Ops.trunc av (knownNat :: NatRepr 32)))

prop_uext_sound :: H.Property
prop_uext_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValue32WithElement
  H.assert (Ops.mayBeMember x (Ops.uext av Gen.w))

prop_bitop_and_sound :: H.Property
prop_bitop_and_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  (bv, y) <- H.forAll Gen.genAbsValueWithElement
  H.assert (Ops.mayBeMember (x .&. y) (Ops.bitop (.&.) Gen.w av bv))

prop_bitop_or_sound :: H.Property
prop_bitop_or_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  (bv, y) <- H.forAll Gen.genAbsValueWithElement
  H.assert (Ops.mayBeMember (x .|. y) (Ops.bitop (.|.) Gen.w av bv))

prop_bitop_xor_sound :: H.Property
prop_bitop_xor_sound = H.property $ do
  (av, x) <- H.forAll Gen.genAbsValueWithElement
  (bv, y) <- H.forAll Gen.genAbsValueWithElement
  H.assert (Ops.mayBeMember (x `xor` y) (Ops.bitop xor Gen.w av bv))

-- ---------------------------------------------------------------------------
-- Bounds (hasMaximum / hasMinimum) and ordering refinement

-- | Whatever 'hasMaximum' returns must fit in the bit-width: otherwise
-- 'abstractULt' / 'abstractULeq' would feed an out-of-range value to
-- 'SI.mkStridedInterval' as a bound.
prop_hasMaximum_canonical :: H.Property
prop_hasMaximum_canonical = H.property $ do
  av <- H.forAll Gen.genAbsValue
  case Ops.hasMaximum Gen.w av of
    Nothing -> H.discard
    Just u  -> do
      H.assert (0 <= u)
      H.assert (u <= maxUnsigned Gen.w)

prop_hasMinimum_canonical :: H.Property
prop_hasMinimum_canonical = H.property $ do
  av <- H.forAll Gen.genAbsValue
  case Ops.hasMinimum Gen.w av of
    Nothing -> H.discard
    Just l  -> do
      H.assert (0 <= l)
      H.assert (l <= maxUnsigned Gen.w)

-- | Soundness: when 'hasMaximum' returns a bound, every concrete member of
-- @av@ is below it.  Returning 'Nothing' is always sound (no claim made).
prop_hasMaximum_upperBound :: H.Property
prop_hasMaximum_upperBound = H.property $ do
  (av, v) <- H.forAll Gen.genAbsValueWithElement
  case Ops.hasMaximum Gen.w av of
    Nothing -> H.discard
    Just u  -> H.assert (v <= u)

-- | Soundness: when 'hasMinimum' returns a bound, every concrete member of
-- @av@ is above it.
prop_hasMinimum_lowerBound :: H.Property
prop_hasMinimum_lowerBound = H.property $ do
  (av, v) <- H.forAll Gen.genAbsValueWithElement
  case Ops.hasMinimum Gen.w av of
    Nothing -> H.discard
    Just l  -> H.assert (l <= v)

-- | If @x < y@ holds for chosen members, the refined pair must still contain
-- those members. A wrapped bound feeding 'mkStridedInterval' would silently
-- exclude valid elements.
prop_abstractULt_sound :: H.Property
prop_abstractULt_sound = H.property $ do
  (p1, p2) <- H.forAll ((,) <$> Gen.genAbsValueWithElement
                            <*> Gen.genAbsValueWithElement)
  let ((av, x), (bv, y)) = if snd p1 < snd p2 then (p1, p2) else (p2, p1)
  if x == y
    then H.discard
    else do
      let (av', bv') = abstractULt Gen.w av bv
      H.assert (Ops.mayBeMember x av')
      H.assert (Ops.mayBeMember y bv')

prop_abstractULeq_sound :: H.Property
prop_abstractULeq_sound = H.property $ do
  (p1, p2) <- H.forAll ((,) <$> Gen.genAbsValueWithElement
                            <*> Gen.genAbsValueWithElement)
  let ((av, x), (bv, y)) = if snd p1 <= snd p2 then (p1, p2) else (p2, p1)
  let (av', bv') = abstractULeq Gen.w av bv
  H.assert (Ops.mayBeMember x av')
  H.assert (Ops.mayBeMember y bv')

-- ---------------------------------------------------------------------------
-- StackOffset-specific properties

prop_stackoffset_bvadd_singleton :: H.Property
prop_stackoffset_bvadd_singleton = H.property $ do
  addr  <- H.forAll Gen.genMemAddr
  off   <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 minBound maxBound) :: H.Gen Int64)
  delta <- H.forAll Gen.genBV
  let sv     = StackOffsetAbsVal addr off :: AbsValue Gen.W (BVType Gen.W)
      result = bvadd Gen.w sv (FinSet (Set.singleton delta))
  case result of
    StackOffsetAbsVal addr' _ -> addr' H.=== addr
    SomeStackOffset addr'     -> addr' H.=== addr
    _                         -> H.discard

prop_stackoffset_join_some :: H.Property
prop_stackoffset_join_some = H.property $ do
  addr <- H.forAll Gen.genMemAddr
  off1 <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 minBound maxBound) :: H.Gen Int64)
  off2 <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 minBound maxBound) :: H.Gen Int64)
  if off1 == off2
    then H.discard
    else lub (StackOffsetAbsVal addr off1 :: AbsValue Gen.W (BVType Gen.W))
             (StackOffsetAbsVal addr off2) H.=== SomeStackOffset addr

-- ---------------------------------------------------------------------------
-- concretize / asConcreteSingleton consistency

prop_concretize_mayBeMember :: H.Property
prop_concretize_mayBeMember = H.property $ do
  av <- H.forAll Gen.genAbsValue
  case concretize av of
    Nothing -> H.discard
    Just s  -> mapM_ (\v -> H.assert (Ops.mayBeMember v av)) (Set.toList s)

prop_asConcreteSingleton_consistent :: H.Property
prop_asConcreteSingleton_consistent = H.property $ do
  av <- H.forAll Gen.genSingleton
  case asConcreteSingleton av of
    Nothing -> H.discard
    Just v  -> do
      concretize av H.=== Just (Set.singleton v)
      H.assert (Ops.mayBeMember v av)

-- ---------------------------------------------------------------------------
-- isBottom consistency

prop_isBottom_concretize :: H.Property
prop_isBottom_concretize = H.property $ do
  av <- H.forAll Gen.genBottom
  H.assert (isBottom av)
  case concretize av of
    Just s  -> H.assert (Set.null s)
    Nothing -> pure ()

-- ---------------------------------------------------------------------------
-- Test tree

tests :: TT.TestTree
tests = TT.testGroup "AbsValue"
  [ TT.testGroup "AbsDomain lattice laws"
    [ TTH.testProperty "top is upper bound" prop_top_upperBound
    , TTH.testProperty "leq reflexive" prop_leq_reflexive
    , TTH.testProperty "lub is upper bound for operands" prop_lub_upper_bound
    , TTH.testProperty "joinD idempotent" prop_joinD_idempotent
    , TTH.testProperty "joinD/lub consistent" prop_joinD_lub_consistent
    ]
  , TT.testGroup "meet (refinement)"
    [ TTH.testProperty "meet lower bound of left operand" prop_meet_lower_bound_left
    , TTH.testProperty "meet lower bound of right operand" prop_meet_lower_bound_right
    , TTH.testProperty "meet sound (shared element is in result)" prop_meet_sound
    , TTH.testProperty "meet commutative" prop_meet_commutative
    , TTH.testProperty "meet idempotent" prop_meet_idempotent
    , TTH.testProperty "meet top identity" prop_meet_top_identity
    ]
  , TT.testGroup "arithmetic soundness"
    [ TTH.testProperty "bvadd sound" prop_bvadd_sound
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
    ]
  , TT.testGroup "bounds and ordering refinement"
    [ TTH.testProperty "hasMaximum is canonical" prop_hasMaximum_canonical
    , TTH.testProperty "hasMinimum is canonical" prop_hasMinimum_canonical
    , TTH.testProperty "hasMaximum is upper bound" prop_hasMaximum_upperBound
    , TTH.testProperty "hasMinimum is lower bound" prop_hasMinimum_lowerBound
    , TTH.testProperty "abstractULt sound" prop_abstractULt_sound
    , TTH.testProperty "abstractULeq sound" prop_abstractULeq_sound
    ]
  , TT.testGroup "StackOffset"
    [ TTH.testProperty "bvadd singleton advances offset" prop_stackoffset_bvadd_singleton
    , TTH.testProperty "join of distinct offsets gives SomeStackOffset" prop_stackoffset_join_some
    ]
  , TT.testGroup "concretize / membership"
    [ TTH.testProperty "concretize satisfies mayBeMember" prop_concretize_mayBeMember
    , TTH.testProperty "asConcreteSingleton consistent" prop_asConcreteSingleton_consistent
    ]
  , TT.testGroup "isBottom"
    [ TTH.testProperty "isBottom implies empty concretize" prop_isBottom_concretize
    ]
  ]
