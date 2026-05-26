{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Property tests for the lattice operations on 'RangePred', 'SubRange',
-- and the per-edge predicate maps used by 'joinInitialBounds'.
module AbsDomain.JumpBoundsTests
  ( tests
  ) where

import           Control.Monad (forM_)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.NatRepr
import           GHC.Natural (Natural)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as H.Gen
import qualified Hedgehog.Range as H.Range
import qualified Test.Tasty as TT
import qualified Test.Tasty.Hedgehog as TTH

import           Data.Macaw.AbsDomain.JumpBounds.Internal
                   ( RangePred(..)
                   , rangeNotTotal
                   , disjoinRangePred
                   , SubRange(..)
                   , disjoinSubRange
                   , joinAddrPredMap
                   , addrPredMapImpliedBy
                   )
import           Data.Macaw.AbsDomain.StackAnalysis (MemVal(..))
import           Data.Macaw.CFG.AssignRhs (MemRepr(..))
import           Data.Macaw.Memory (Endianness(..))
import           Data.Macaw.Types (BVType)

------------------------------------------------------------------------
-- Width and generators

type W = 8

w :: NatRepr W
w = knownNat @W

-- | Maximum unsigned value at width W.
maxU :: Natural
maxU = fromInteger (maxUnsigned w)

-- | Generate a saturated (l == 0, h == maxU) range — the @top@ of the lattice.
genTop :: H.Gen (RangePred W)
genTop = pure (RangePred w 0 maxU)

-- | Generate an arbitrary 'RangePred' with @lower <= upper@. The range
-- may be saturated (top) or non-saturated (a real fact).
genRangePred :: H.Gen (RangePred W)
genRangePred = do
  l <- H.Gen.integral (H.Range.linear 0 maxU)
  h <- H.Gen.integral (H.Range.linear l maxU)
  pure (RangePred w l h)

-- | Generate only non-saturated 'RangePred's: ones for which 'rangeNotTotal'
-- holds. The 'Maybe' wrappers in 'disjoinRangePred' encode @top@ as 'Nothing',
-- so well-formed inputs to 'disjoinRangePred' should be non-total.
genNonTotalRangePred :: H.Gen (RangePred W)
genNonTotalRangePred = H.Gen.filter rangeNotTotal genRangePred

-- | Lift the 'Maybe' into the lattice: 'Nothing' is @top@.
asRange :: Maybe (RangePred W) -> RangePred W
asRange Nothing  = RangePred w 0 maxU
asRange (Just r) = r

-- | Standard semantic membership predicate on 'RangePred'.
inRange :: RangePred u -> Natural -> Bool
inRange r v = rangeLowerBound r <= v && v <= rangeUpperBound r

-- | Order on 'RangePred': @sub@ is included in @sup@ when @sup@ permits at
-- least every value @sub@ does. Treats 'Maybe' as: 'Nothing' = top, so
-- everything is included in 'Nothing'.
includes :: Maybe (RangePred W) -> Maybe (RangePred W) -> Bool
includes _      Nothing  = True
includes Nothing _       = False -- top can't be inside a non-top
includes (Just sub) (Just sup) =
  rangeLowerBound sup <= rangeLowerBound sub
  && rangeUpperBound sub <= rangeUpperBound sup

------------------------------------------------------------------------
-- disjoinRangePred properties

prop_disjoinRangePred_idempotent :: H.Property
prop_disjoinRangePred_idempotent = H.property $ do
  r <- H.forAll genNonTotalRangePred
  let res = disjoinRangePred r r
  case res of
    Nothing -> H.failure   -- @r ∪ r@ should not become top if @r@ wasn't
    Just j  -> do
      rangeLowerBound j H.=== rangeLowerBound r
      rangeUpperBound j H.=== rangeUpperBound r

prop_disjoinRangePred_commutative :: H.Property
prop_disjoinRangePred_commutative = H.property $ do
  a <- H.forAll genRangePred
  b <- H.forAll genRangePred
  let xy = disjoinRangePred a b
      yx = disjoinRangePred b a
  -- Compare via lower/upper bounds (RangePred has no Eq instance).
  fmap rangeLowerBound xy H.=== fmap rangeLowerBound yx
  fmap rangeUpperBound xy H.=== fmap rangeUpperBound yx
  -- And widths agree:
  fmap (natValue . rangeWidth) xy H.=== fmap (natValue . rangeWidth) yx

prop_disjoinRangePred_associative :: H.Property
prop_disjoinRangePred_associative = H.property $ do
  a <- H.forAll genRangePred
  b <- H.forAll genRangePred
  c <- H.forAll genRangePred
  -- (a ∪ b) ∪ c = a ∪ (b ∪ c) under the @Maybe = top@ encoding.
  let lhs = case disjoinRangePred a b of
              Nothing -> Nothing
              Just ab -> disjoinRangePred ab c
      rhs = case disjoinRangePred b c of
              Nothing -> Nothing
              Just bc -> disjoinRangePred a bc
  fmap rangeLowerBound lhs H.=== fmap rangeLowerBound rhs
  fmap rangeUpperBound lhs H.=== fmap rangeUpperBound rhs

prop_disjoinRangePred_top_left :: H.Property
prop_disjoinRangePred_top_left = H.property $ do
  -- @top ∪ x = top@: we don't have a direct call form because the API only
  -- accepts non-Nothing inputs, so we model @top@ as "any range whose
  -- union with x saturates."
  r   <- H.forAll genRangePred
  top <- H.forAll genTop
  case disjoinRangePred top r of
    Nothing -> H.success
    Just _  -> H.failure

-- | Soundness: any concrete value satisfying @a@ or @b@ also satisfies
-- @a ∪ b@.  This is the membership-level lattice soundness condition.
prop_disjoinRangePred_sound :: H.Property
prop_disjoinRangePred_sound = H.property $ do
  a <- H.forAll genRangePred
  b <- H.forAll genRangePred
  va <- H.forAll (H.Gen.integral (H.Range.linear (rangeLowerBound a) (rangeUpperBound a)))
  vb <- H.forAll (H.Gen.integral (H.Range.linear (rangeLowerBound b) (rangeUpperBound b)))
  let u = asRange (disjoinRangePred a b)
  H.assert (inRange u va)
  H.assert (inRange u vb)

prop_disjoinRangePred_ordering :: H.Property
prop_disjoinRangePred_ordering = H.property $ do
  -- @x ⊑ x ∪ y@ and @y ⊑ x ∪ y@ in our @Maybe = top@ ordering.
  a <- H.forAll genRangePred
  b <- H.forAll genRangePred
  let u = disjoinRangePred a b
  H.assert (includes (Just a) u)
  H.assert (includes (Just b) u)

prop_disjoinRangePred_saturates_when_total :: H.Property
prop_disjoinRangePred_saturates_when_total = H.property $ do
  -- If the union covers @[0, maxU]@, the result must be 'Nothing' (top).
  a <- H.forAll genRangePred
  b <- H.forAll genRangePred
  let l = min (rangeLowerBound a) (rangeLowerBound b)
      h = max (rangeUpperBound a) (rangeUpperBound b)
      r = disjoinRangePred a b
  if l == 0 && h == maxU
    then case r of
           Nothing -> H.success
           Just _  -> H.failure
    else case r of
           Just j -> do
             rangeLowerBound j H.=== l
             rangeUpperBound j H.=== h
           Nothing -> H.failure

------------------------------------------------------------------------
-- disjoinSubRange properties (these mostly reduce to disjoinRangePred,
-- but also exercise the bit-width gate)

genSubRangeW :: H.Gen (SubRange (BVType W))
genSubRangeW = SubRange <$> genRangePred

subRangeBounds :: Maybe (SubRange (BVType W)) -> Maybe (Natural, Natural)
subRangeBounds Nothing            = Nothing
subRangeBounds (Just (SubRange r)) = Just (rangeLowerBound r, rangeUpperBound r)

subRangeNotTotal :: SubRange (BVType W) -> Bool
subRangeNotTotal (SubRange r) = rangeNotTotal r

showSubRange :: SubRange (BVType W) -> String
showSubRange (SubRange r) =
  "SubRange " ++ show (rangeLowerBound r) ++ " " ++ show (rangeUpperBound r)

prop_disjoinSubRange_commutative :: H.Property
prop_disjoinSubRange_commutative = H.property $ do
  a <- H.forAllWith showSubRange genSubRangeW
  b <- H.forAllWith showSubRange genSubRangeW
  subRangeBounds (disjoinSubRange a b) H.=== subRangeBounds (disjoinSubRange b a)

prop_disjoinSubRange_idempotent :: H.Property
prop_disjoinSubRange_idempotent = H.property $ do
  s <- H.forAllWith showSubRange (H.Gen.filter subRangeNotTotal genSubRangeW)
  let original = subRangeBounds (Just s)
  subRangeBounds (disjoinSubRange s s) H.=== original

prop_disjoinSubRange_associative :: H.Property
prop_disjoinSubRange_associative = H.property $ do
  a <- H.forAllWith showSubRange genSubRangeW
  b <- H.forAllWith showSubRange genSubRangeW
  c <- H.forAllWith showSubRange genSubRangeW
  let lhs = case disjoinSubRange a b of
              Nothing -> Nothing
              Just ab -> disjoinSubRange ab c
      rhs = case disjoinSubRange b c of
              Nothing -> Nothing
              Just bc -> disjoinSubRange a bc
  subRangeBounds lhs H.=== subRangeBounds rhs

prop_disjoinSubRange_top_absorbs :: H.Property
prop_disjoinSubRange_top_absorbs = H.property $ do
  s <- H.forAllWith showSubRange genSubRangeW
  let top = SubRange (RangePred w 0 maxU)
  case disjoinSubRange top s of
    Nothing -> H.success
    Just _  -> H.failure

-- | Soundness: any concrete value satisfying @a@ or @b@ also satisfies
-- @a ∪ b@.
prop_disjoinSubRange_sound :: H.Property
prop_disjoinSubRange_sound = H.property $ do
  sa@(SubRange ra) <- H.forAllWith showSubRange genSubRangeW
  sb@(SubRange rb) <- H.forAllWith showSubRange genSubRangeW
  va <- H.forAll (H.Gen.integral
                    (H.Range.linear (rangeLowerBound ra) (rangeUpperBound ra)))
  vb <- H.forAll (H.Gen.integral
                    (H.Range.linear (rangeLowerBound rb) (rangeUpperBound rb)))
  let u = subRangeBounds (disjoinSubRange sa sb)
      isIn (Just (l, h)) v = l <= v && v <= h
      isIn Nothing       _ = True   -- top contains everything
  H.assert (isIn u va)
  H.assert (isIn u vb)

prop_disjoinSubRange_ordering :: H.Property
prop_disjoinSubRange_ordering = H.property $ do
  -- @x ⊑ x ∪ y@ and @y ⊑ x ∪ y@ in the @Nothing = top@ ordering.
  sa <- H.forAllWith showSubRange genSubRangeW
  sb <- H.forAllWith showSubRange genSubRangeW
  let u = subRangeBounds (disjoinSubRange sa sb)
      sub = subRangeBounds . Just
      includesSub _      Nothing      = True
      includesSub Nothing _           = False
      includesSub (Just (la, ha)) (Just (lu, hu)) = lu <= la && ha <= hu
  H.assert (includesSub (sub sa) u)
  H.assert (includesSub (sub sb) u)

prop_disjoinSubRange_saturates_when_total :: H.Property
prop_disjoinSubRange_saturates_when_total = H.property $ do
  sa@(SubRange ra) <- H.forAllWith showSubRange genSubRangeW
  sb@(SubRange rb) <- H.forAllWith showSubRange genSubRangeW
  let l = min (rangeLowerBound ra) (rangeLowerBound rb)
      h = max (rangeUpperBound ra) (rangeUpperBound rb)
      r = disjoinSubRange sa sb
  if l == 0 && h == maxU
    then case r of
           Nothing -> H.success
           Just _  -> H.failure
    else case subRangeBounds r of
           Just (lj, hj) -> do
             lj H.=== l
             hj H.=== h
           Nothing -> H.failure

------------------------------------------------------------------------
-- joinAddrPredMap properties

-- | Generate a small finite address space so we get useful intersection.
genAddrKey :: H.Gen Int
genAddrKey = H.Gen.integral (H.Range.linear 0 4)

genAddrEntry :: H.Gen (Int, MemVal SubRange)
genAddrEntry = do
  k <- genAddrKey
  s <- genSubRangeW
  pure (k, MemVal (BVMemRepr (knownNat @1) LittleEndian) s)

genAddrMap :: H.Gen (Map Int (MemVal SubRange))
genAddrMap = Map.fromList <$> H.Gen.list (H.Range.linear 0 6) genAddrEntry

showAddrMap :: Map Int (MemVal SubRange) -> String
showAddrMap = show . Map.toList . fmap memValBounds

prop_joinAddrPredMap_keys_subset :: H.Property
prop_joinAddrPredMap_keys_subset = H.property $ do
  -- Result keys are a subset of (and in fact intersection of) the input keys.
  a <- H.forAllWith showAddrMap genAddrMap
  b <- H.forAllWith showAddrMap genAddrMap
  let j = joinAddrPredMap a b
  H.assert (all (`Map.member` a) (Map.keys j))
  H.assert (all (`Map.member` b) (Map.keys j))

-- | Extract @(lower, upper)@ bounds from a 'MemVal SubRange', collapsing
-- existentials so we can compare with 'Eq'.
memValBounds :: MemVal SubRange -> (Natural, Natural)
memValBounds (MemVal _ (SubRange r)) = (rangeLowerBound r, rangeUpperBound r)

prop_joinAddrPredMap_idempotent :: H.Property
prop_joinAddrPredMap_idempotent = H.property $ do
  a <- H.forAllWith showAddrMap genAddrMap
  let j = joinAddrPredMap a a
  H.assert (addrPredMapImpliedBy a j)
  -- And every entry in the original is preserved (idempotent under join):
  Map.keys j H.=== Map.keys a

prop_joinAddrPredMap_commutative :: H.Property
prop_joinAddrPredMap_commutative = H.property $ do
  a <- H.forAllWith showAddrMap genAddrMap
  b <- H.forAllWith showAddrMap genAddrMap
  let xy = joinAddrPredMap a b
      yx = joinAddrPredMap b a
  -- Compare by extracting (lo, hi) per key, since MemVal has no Eq.
  fmap memValBounds xy H.=== fmap memValBounds yx

prop_joinAddrPredMap_widens :: H.Property
prop_joinAddrPredMap_widens = H.property $ do
  -- Every fact in @a@ that survives should be at least as wide as the
  -- original fact in @a@.
  a <- H.forAllWith showAddrMap genAddrMap
  b <- H.forAllWith showAddrMap genAddrMap
  let j = joinAddrPredMap a b
  let surviving = Map.intersectionWith (,) (fmap memValBounds a) (fmap memValBounds j)
  H.assert (all widensCorrectly (Map.elems surviving))
  where
    widensCorrectly ((la, ha), (lj, hj)) = lj <= la && hj >= ha

prop_joinAddrPredMap_associative :: H.Property
prop_joinAddrPredMap_associative = H.property $ do
  a <- H.forAllWith showAddrMap genAddrMap
  b <- H.forAllWith showAddrMap genAddrMap
  c <- H.forAllWith showAddrMap genAddrMap
  let lhs = joinAddrPredMap (joinAddrPredMap a b) c
      rhs = joinAddrPredMap a (joinAddrPredMap b c)
  fmap memValBounds lhs H.=== fmap memValBounds rhs

-- | An empty map is the @top@/identity of the lattice: the join produces
-- no surviving facts (no key is present in both @top@ and any non-empty
-- map at every key).
prop_joinAddrPredMap_top_left :: H.Property
prop_joinAddrPredMap_top_left = H.property $ do
  a <- H.forAllWith showAddrMap genAddrMap
  -- "top" in this lattice is the map that asserts no facts: i.e. the empty
  -- map. Joining anything with the empty map drops every fact.
  let j = joinAddrPredMap Map.empty a
  Map.null j H.=== True

-- | Soundness: at every key in the joined map, any concrete value that
-- satisfies either input's fact at that key also satisfies the joined fact.
-- This is the membership-level lattice soundness condition.
prop_joinAddrPredMap_sound :: H.Property
prop_joinAddrPredMap_sound = H.property $ do
  a <- H.forAllWith showAddrMap genAddrMap
  b <- H.forAllWith showAddrMap genAddrMap
  let j  = joinAddrPredMap a b
      ab = fmap memValBounds a
      bb = fmap memValBounds b
      jb = fmap memValBounds j
  -- For each surviving key, generate concrete elements satisfying @a@'s
  -- and @b@'s facts at that key and check they fall in the joined range.
  forM_ (Map.keys jb) $ \k -> do
    let Just (lj, hj) = Map.lookup k jb
    case Map.lookup k ab of
      Just (la, ha) -> do
        va <- H.forAll (H.Gen.integral (H.Range.linear la ha))
        H.assert (lj <= va && va <= hj)
      Nothing -> H.failure  -- surviving key must be in @a@
    case Map.lookup k bb of
      Just (lb, hb) -> do
        vb <- H.forAll (H.Gen.integral (H.Range.linear lb hb))
        H.assert (lj <= vb && vb <= hj)
      Nothing -> H.failure  -- surviving key must be in @b@

prop_joinAddrPredMap_ordering :: H.Property
prop_joinAddrPredMap_ordering = H.property $ do
  -- @addrPredMapImpliedBy old joined@ holds when every key in @old@ has a
  -- *narrower* range in @joined@ — i.e., @joined@ is a refinement (stronger)
  -- of @old@. After a real join, the result is *weaker* than both inputs,
  -- so the input maps refine the joined map at every surviving key.
  a <- H.forAllWith showAddrMap genAddrMap
  b <- H.forAllWith showAddrMap genAddrMap
  let j = joinAddrPredMap a b
  H.assert (addrPredMapImpliedBy j a)
  H.assert (addrPredMapImpliedBy j b)

prop_addrPredMapImpliedBy_reflexive :: H.Property
prop_addrPredMapImpliedBy_reflexive = H.property $ do
  a <- H.forAllWith showAddrMap genAddrMap
  H.assert (addrPredMapImpliedBy a a)

-- | Build a map looser than the input: keys are a subset, and at each
-- shared key, the bounds are wider (lower bound at most as large, upper
-- bound at least as large). The result @looser@ satisfies
-- @addrPredMapImpliedBy looser m@.
--
-- All generated entries use the same fixed @MemRepr@ as 'genAddrEntry', so
-- we reconstruct fresh 'MemVal's rather than reusing the existential
-- 'MemRepr' from the input.
genLooser :: Map Int (MemVal SubRange) -> H.Gen (Map Int (MemVal SubRange))
genLooser m = do
  ks <- H.Gen.subsequence (Map.keys m)
  fmap Map.fromList $ traverse loosenAt ks
  where
    loosenAt k = do
      let Just (oldLo, oldHi) = fmap memValBounds (Map.lookup k m)
      newLo <- H.Gen.integral (H.Range.linear 0 oldLo)
      newHi <- H.Gen.integral (H.Range.linear oldHi maxU)
      pure ( k
           , MemVal (BVMemRepr (knownNat @1) LittleEndian)
                    (SubRange (RangePred w newLo newHi))
           )

-- | Sanity check on 'genLooser': any map it produces from @m@ is implied
-- by @m@. If this fails, the transitive/antisymmetric tests below are
-- testing nothing useful.
prop_genLooser_isLooser :: H.Property
prop_genLooser_isLooser = H.property $ do
  m      <- H.forAllWith showAddrMap genAddrMap
  looser <- H.forAllWith showAddrMap (genLooser m)
  H.assert (addrPredMapImpliedBy looser m)

prop_addrPredMapImpliedBy_transitive :: H.Property
prop_addrPredMapImpliedBy_transitive = H.property $ do
  -- Build a chain c (tightest) ⊑ b ⊑ a (loosest), so that
  -- @a impliedBy b@ and @b impliedBy c@ hold by construction.
  c <- H.forAllWith showAddrMap genAddrMap
  b <- H.forAllWith showAddrMap (genLooser c)
  a <- H.forAllWith showAddrMap (genLooser b)
  -- Sanity-check the construction:
  H.assert (addrPredMapImpliedBy a b)
  H.assert (addrPredMapImpliedBy b c)
  -- Transitivity: a is implied by c.
  H.assert (addrPredMapImpliedBy a c)


------------------------------------------------------------------------
-- Test tree

tests :: TT.TestTree
tests = TT.testGroup "JumpBounds"
  [ TT.testGroup "disjoinRangePred"
      [ TTH.testProperty "idempotent"             prop_disjoinRangePred_idempotent
      , TTH.testProperty "commutative"            prop_disjoinRangePred_commutative
      , TTH.testProperty "associative"            prop_disjoinRangePred_associative
      , TTH.testProperty "top absorbs"            prop_disjoinRangePred_top_left
      , TTH.testProperty "sound (membership)"     prop_disjoinRangePred_sound
      , TTH.testProperty "ordering"               prop_disjoinRangePred_ordering
      , TTH.testProperty "saturates when total"   prop_disjoinRangePred_saturates_when_total
      ]
  , TT.testGroup "disjoinSubRange"
      [ TTH.testProperty "commutative"            prop_disjoinSubRange_commutative
      , TTH.testProperty "idempotent"             prop_disjoinSubRange_idempotent
      , TTH.testProperty "associative"            prop_disjoinSubRange_associative
      , TTH.testProperty "top absorbs"            prop_disjoinSubRange_top_absorbs
      , TTH.testProperty "sound (membership)"     prop_disjoinSubRange_sound
      , TTH.testProperty "ordering"               prop_disjoinSubRange_ordering
      , TTH.testProperty "saturates when total"   prop_disjoinSubRange_saturates_when_total
      ]
  , TT.testGroup "joinAddrPredMap"
      [ TTH.testProperty "keys subset of inputs"  prop_joinAddrPredMap_keys_subset
      , TTH.testProperty "idempotent"             prop_joinAddrPredMap_idempotent
      , TTH.testProperty "commutative"            prop_joinAddrPredMap_commutative
      , TTH.testProperty "associative"            prop_joinAddrPredMap_associative
      , TTH.testProperty "empty is top (left)"    prop_joinAddrPredMap_top_left
      , TTH.testProperty "sound (membership)"     prop_joinAddrPredMap_sound
      , TTH.testProperty "ordering"               prop_joinAddrPredMap_ordering
      , TTH.testProperty "widens surviving facts" prop_joinAddrPredMap_widens
      , TTH.testProperty "impliedBy reflexive"    prop_addrPredMapImpliedBy_reflexive
      , TTH.testProperty "genLooser is looser"    prop_genLooser_isLooser
      , TTH.testProperty "impliedBy transitive"   prop_addrPredMapImpliedBy_transitive
      ]
  ]

