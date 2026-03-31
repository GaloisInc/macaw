{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Common (tests) where

import qualified Data.BitVector.Sized as BV
import qualified Data.IntervalMap.Strict as IM
import qualified Data.IntervalMap.Interval as IMI
import           GHC.TypeLits (KnownNat, type (<=))
import           Data.Word (Word32, Word64)
import           Numeric.Natural (Natural)

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Symbolic as MS
import           Data.Macaw.Symbolic.Memory.Common
                   ( MutableIntervalMap(..)
                   , ImmutableIntervalMap(..)
                   , mkGlobalPointerValidityPredCommon
                   , defaultProcessMacawAssertion
                   )
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.LLVM.MemModel.Pointer as CLP
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified What4.Expr as WE
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.HUnit ((@?=), testCase)
import           Test.Tasty.Hedgehog (testPropertyNamed)

import           Utils (withSym, mkPtr)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- | Wrap an LLVMPointer in a RegEntry.
mkRegEntry :: (1 <= w, KnownNat w) => CL.LLVMPtr sym w -> CS.RegEntry sym (CL.LLVMPointerType w)
mkRegEntry ptr = CS.RegEntry (CL.LLVMPointerRepr WI.knownNat) ptr

-- | The result of evaluating a validity predicate on a pointer.
data ValidityResult
  = NonGlobalBlock
    -- ^ The pointer's block ID is a known non-zero constant, so the
    -- validity predicate does not apply (returns 'Nothing').
  | ValidityTrue
    -- ^ The predicate simplified to 'True' (access is valid).
  | ValidityFalse
    -- ^ The predicate simplified to 'False' (access is invalid).
  | ValiditySymbolic
    -- ^ The predicate could not be simplified to a constant
    -- (e.g., because the pointer offset is symbolic).
  deriving (Eq, Show)

-- | Extract the validity result from the raw output of
-- 'mkGlobalPointerValidityPredCommon'.
extractValidityResult ::
  Maybe (CB.LabeledPred (WEB.BoolExpr t) e) ->
  ValidityResult
extractValidityResult Nothing = NonGlobalBlock
extractValidityResult (Just (CB.LabeledPred p _)) = case WI.asConstantPred p of
  Just True  -> ValidityTrue
  Just False -> ValidityFalse
  Nothing    -> ValiditySymbolic

-- | Split (lo, hi, mutability) triples into separate mutable and immutable
-- IntervalMaps, matching the split-map API of mkGlobalPointerValidityPredCommon.
mkSplitMaps ::
  forall w.
  MC.MemWidth w =>
  [(Word64, Word64, CL.Mutability)] ->
  ( MutableIntervalMap (MC.MemWord w) ()
  , ImmutableIntervalMap (MC.MemWord w) ()
  )
mkSplitMaps entries =
  ( MutableIntervalMap $ IM.fromList
      [ (iv, ()) | (lo, hi, CL.Mutable)   <- entries
                  , let iv = IMI.IntervalCO (fromIntegral lo) (fromIntegral hi) ]
  , ImmutableIntervalMap $ IM.fromList
      [ (iv, ()) | (lo, hi, CL.Immutable) <- entries
                  , let iv = IMI.IntervalCO (fromIntegral lo) (fromIntegral hi) ]
  )

-- | Parameterized test for mkGlobalPointerValidityPredCommon.
testValidityPred ::
  String ->
  [(Word64, Word64, CL.Mutability)] ->
  Natural ->
  Word64 ->
  MS.PointerUseTag ->
  Maybe Bool ->
  -- ^ Optional condition (Nothing = unconditional, Just False = conditional
  -- access with false condition)
  ValidityResult ->
  TestTree
testValidityPred name intervals blk off tag mcondVal expected =
  testCase name $ do
    result <- withSym $ \sym -> do
      let ?processMacawAssert = defaultProcessMacawAssertion
      let (mutMap, immutMap) = mkSplitMaps @32 intervals
      let puse = MS.PointerUse Nothing tag
      ptr <- mkPtr sym MC.Addr32 blk off
      let ptrEntry = mkRegEntry ptr
      mcondEntry <- case mcondVal of
        Nothing -> pure Nothing
        Just b -> do
          let p = if b then WI.truePred sym else WI.falsePred sym
          pure (Just (CS.RegEntry CT.BoolRepr p))
      extractValidityResult <$>
        mkGlobalPointerValidityPredCommon mutMap immutMap sym puse mcondEntry ptrEntry
    result @?= expected

-- | Like testValidityPred but for a symbolic block ID.
testValidityPredSymbolicBlock ::
  String ->
  [(Word64, Word64, CL.Mutability)] ->
  Word64 ->
  MS.PointerUseTag ->
  ValidityResult ->
  TestTree
testValidityPredSymbolicBlock name intervals off tag expected =
  testCase name $ do
    result <- withSym $ \sym -> do
      let ?processMacawAssert = defaultProcessMacawAssertion
      let (mutMap, immutMap) = mkSplitMaps @32 intervals
      let puse = MS.PointerUse Nothing tag
      blkSym <- WI.freshNat sym (WI.safeSymbol "blk")
      offSym <- WI.bvLit sym (WI.knownNat @32)
                  (BV.mkBV (WI.knownNat @32) (fromIntegral @Word64 @Integer off))
      let ptr = CLP.LLVMPointer blkSym offSym
      let ptrEntry = mkRegEntry ptr
      extractValidityResult <$>
        mkGlobalPointerValidityPredCommon mutMap immutMap sym puse Nothing ptrEntry
    result @?= expected

-- | Test with a symbolic offset that is an ite of two concrete values.
-- The pointer has block 0 and offset @ite freshBool off1 off2@.
testValidityPredIteOffset ::
  String ->
  [(Word64, Word64, CL.Mutability)] ->
  Word64 ->
  Word64 ->
  MS.PointerUseTag ->
  ValidityResult ->
  TestTree
testValidityPredIteOffset name intervals off1 off2 tag expected =
  testCase name $ do
    result <- withSym $ \sym -> do
      let ?processMacawAssert = defaultProcessMacawAssertion
      let (mutMap, immutMap) = mkSplitMaps @32 intervals
      let puse = MS.PointerUse Nothing tag
      blkSym <- WI.natLit sym 0
      let w32 = WI.knownNat @32
      bv1 <- WI.bvLit sym w32 (BV.mkBV w32 (fromIntegral off1))
      bv2 <- WI.bvLit sym w32 (BV.mkBV w32 (fromIntegral off2))
      cond <- WI.freshConstant sym (WI.safeSymbol "c") CT.BaseBoolRepr
      offSym <- WI.bvIte sym cond bv1 bv2
      let ptr = CLP.LLVMPointer blkSym offSym
      let ptrEntry = mkRegEntry ptr
      extractValidityResult <$>
        mkGlobalPointerValidityPredCommon mutMap immutMap sym puse Nothing ptrEntry
    result @?= expected

------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Shared memory model"
  [ testGroup "mkGlobalPointerValidityPredCommon"
      [ testGroup "Basic access"
          [ testValidityPred
              "Read from mutable region"
              [(100, 200, CL.Mutable)]
              0
              150
              MS.PointerRead
              Nothing
              ValidityTrue
          , testValidityPred
              "Read from immutable region"
              [(100, 200, CL.Immutable)]
              0
              150
              MS.PointerRead
              Nothing
              ValidityTrue
          , testValidityPred
              "Write to mutable region"
              [(100, 200, CL.Mutable)]
              0
              150
              MS.PointerWrite
              Nothing
              ValidityTrue
          , testValidityPred
              "Write to immutable region (rejected)"
              [(100, 200, CL.Immutable)]
              0
              150
              MS.PointerWrite
              Nothing
              ValidityFalse
          ]
      , testGroup "Unmapped access"
          [ testValidityPred
              "Read from unmapped region"
              [(100, 200, CL.Mutable)]
              0
              300
              MS.PointerRead
              Nothing
              ValidityFalse
          , testValidityPred
              "Write to unmapped region"
              [(100, 200, CL.Mutable)]
              0
              300
              MS.PointerWrite
              Nothing
              ValidityFalse
          , testValidityPred
              "Empty map"
              []
              0
              100
              MS.PointerRead
              Nothing
              ValidityFalse
          ]
      , testGroup "Block ID"
          [ testValidityPred
              "Non-zero block returns Nothing"
              [(100, 200, CL.Mutable)]
              1
              150
              MS.PointerRead
              Nothing
              NonGlobalBlock
          , testValidityPredSymbolicBlock
              "Symbolic block, in-range offset simplifies to True"
              [(100, 200, CL.Mutable)]
              150
              MS.PointerRead
              ValidityTrue  -- ite (blk==0) True True = True
          , testValidityPredSymbolicBlock
              "Symbolic block, out-of-range offset is non-trivial"
              [(100, 200, CL.Mutable)]
              300
              MS.PointerRead
              ValiditySymbolic  -- ite (blk==0) False True — not simplifiable
          ]
      , testGroup "Boundary conditions"
          [ testValidityPred
              "At lower bound (inclusive)"
              [(100, 200, CL.Mutable)]
              0
              100
              MS.PointerRead
              Nothing
              ValidityTrue
          , testValidityPred
              "At upper bound (exclusive)"
              [(100, 200, CL.Mutable)]
              0
              200
              MS.PointerRead
              Nothing
              ValidityFalse
          ]
      , testGroup "Conditional writes"
          [ testValidityPred
              "Conditional write with false condition is trivially true"
              [(100, 200, CL.Immutable)]
              0
              150
              MS.PointerWrite
              (Just False)
              ValidityTrue
          ]
      , testGroup "Symbolic offsets (ite of two concrete values)"
          [ testValidityPredIteOffset
              "Both branches in range"
              [(100, 200, CL.Mutable)]
              150  -- in range
              160  -- in range
              MS.PointerRead
              ValidityTrue
          , testValidityPredIteOffset
              "Both branches out of range"
              [(100, 200, CL.Mutable)]
              50   -- out of range
              300  -- out of range
              MS.PointerRead
              ValiditySymbolic  -- non-trivial (What4 can't simplify through range checks)
          , testValidityPredIteOffset
              "One branch in range, one out"
              [(100, 200, CL.Mutable)]
              150  -- in range
              300  -- out of range
              MS.PointerRead
              ValiditySymbolic  -- non-trivial
          , testValidityPredIteOffset
              "Write with one branch in mutable, one in immutable"
              [(100, 200, CL.Mutable), (300, 400, CL.Immutable)]
              150  -- in mutable (write OK)
              350  -- in immutable (write rejected)
              MS.PointerWrite
              ValiditySymbolic  -- non-trivial
          , testValidityPredIteOffset
              "Read with one branch in mutable, one in immutable"
              [(100, 200, CL.Mutable), (300, 400, CL.Immutable)]
              150  -- in mutable
              350  -- in immutable
              MS.PointerRead
              ValiditySymbolic  -- non-trivial (What4 can't simplify through range checks)
          , testValidityPredIteOffset
              "Branches straddle lower bound"
              [(100, 200, CL.Mutable)]
              99   -- just below
              100  -- at bound (inclusive)
              MS.PointerRead
              ValiditySymbolic  -- non-trivial
          , testValidityPredIteOffset
              "Branches straddle upper bound"
              [(100, 200, CL.Mutable)]
              199  -- in range
              200  -- at bound (exclusive, out of range)
              MS.PointerRead
              ValiditySymbolic  -- non-trivial
          ]
      ]
  , testGroup "Property-based tests"
      [ testPropertyNamed
          "Write-valid implies read-valid"
          "prop_writeValidImpliesReadValid"
          prop_writeValidImpliesReadValid
      , testPropertyNamed
          "Concrete block-0 pointer always produces decidable predicate"
          "prop_concreteBlock0Decidable"
          prop_concreteBlock0Decidable
      , testPropertyNamed
          "Non-zero concrete block always returns Nothing"
          "prop_nonZeroBlockNothing"
          prop_nonZeroBlockNothing
      , testPropertyNamed
          "False condition makes any access trivially True"
          "prop_falseCondTriviallyTrue"
          prop_falseCondTriviallyTrue
      , testPropertyNamed
          "ite'd pointer agrees when both branches agree"
          "prop_itePointerAgreesWhenBranchesAgree"
          prop_itePointerAgreesWhenBranchesAgree
      , testPropertyNamed
          "ite write-valid implies ite read-not-invalid"
          "prop_iteWriteValidImpliesReadValid"
          prop_iteWriteValidImpliesReadValid
      ]
  ]

------------------------------------------------------------------------
-- Generators
------------------------------------------------------------------------

-- | A single interval entry for the mutability map.
data IntervalEntry = IntervalEntry
  { ieLo  :: !Word32
  , ieHi  :: !Word32
  , ieMut :: !CL.Mutability
  } deriving (Show)

-- | Generate a non-empty list of non-overlapping interval entries,
-- sorted by base address.
genIntervalEntries :: H.Gen [IntervalEntry]
genIntervalEntries = do
  n <- Gen.int (Range.linear 1 8)
  go n 0 []
  where
    go 0 _ acc = pure (reverse acc)
    go remaining cursor acc = do
      gap <- Gen.word32 (Range.linear 0 100)
      size <- Gen.word32 (Range.linear 1 200)
      mut <- Gen.element [CL.Mutable, CL.Immutable]
      let lo = cursor + gap
          hi = lo + size
      -- Guard against overflow
      if hi <= lo
        then pure (reverse acc)
        else go (remaining - 1) hi (IntervalEntry lo hi mut : acc)

entriesToSplitMaps ::
  [IntervalEntry] ->
  ( MutableIntervalMap (MC.MemWord 32) ()
  , ImmutableIntervalMap (MC.MemWord 32) ()
  )
entriesToSplitMaps entries =
  ( MutableIntervalMap $ IM.fromList
      [ (iv, ()) | e <- entries, ieMut e == CL.Mutable
                  , let iv = IMI.IntervalCO (fromIntegral (ieLo e)) (fromIntegral (ieHi e)) ]
  , ImmutableIntervalMap $ IM.fromList
      [ (iv, ()) | e <- entries, ieMut e == CL.Immutable
                  , let iv = IMI.IntervalCO (fromIntegral (ieLo e)) (fromIntegral (ieHi e)) ]
  )

genOffset :: H.Gen Word32
genOffset = Gen.word32 (Range.linearFrom 100 0 maxBound)

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

-- | Helper to run mkGlobalPointerValidityPredCommon with concrete block-0 pointer.
runValidityPred ::
  WEB.ExprBuilder t WE.EmptyExprBuilderState (WEB.Flags WEB.FloatIEEE) ->
  MutableIntervalMap (MC.MemWord 32) () ->
  ImmutableIntervalMap (MC.MemWord 32) () ->
  Word32 ->
  MS.PointerUseTag ->
  Maybe (CS.RegEntry (WEB.ExprBuilder t WE.EmptyExprBuilderState (WEB.Flags WEB.FloatIEEE)) CT.BoolType) ->
  IO ValidityResult
runValidityPred sym mutMap immutMap off tag mcondEntry = do
  let ?processMacawAssert = defaultProcessMacawAssertion
  let puse = MS.PointerUse Nothing tag
  ptr <- mkPtr sym MC.Addr32 0 (fromIntegral off)
  let ptrEntry = mkRegEntry ptr
  extractValidityResult <$>
    mkGlobalPointerValidityPredCommon mutMap immutMap sym puse mcondEntry ptrEntry

-- | Generate an offset that is likely to land in a mapped region.
genOffsetInEntries :: [IntervalEntry] -> H.Gen Word32
genOffsetInEntries [] = genOffset
genOffsetInEntries entries = Gen.choice
  [ -- Pick a random offset within one of the intervals
    do e <- Gen.element entries
       Gen.word32 (Range.linear (ieLo e) (ieHi e - 1))
  , -- Sometimes pick a random offset (may miss)
    genOffset
  ]

-- | Helper to run mkGlobalPointerValidityPredCommon with an ite'd block-0 pointer.
runValidityPredIte ::
  WEB.ExprBuilder t WE.EmptyExprBuilderState (WEB.Flags WEB.FloatIEEE) ->
  MutableIntervalMap (MC.MemWord 32) () ->
  ImmutableIntervalMap (MC.MemWord 32) () ->
  Word32 ->
  Word32 ->
  MS.PointerUseTag ->
  IO ValidityResult
runValidityPredIte sym mutMap immutMap off1 off2 tag = do
  let ?processMacawAssert = defaultProcessMacawAssertion
  let puse = MS.PointerUse Nothing tag
  let w32 = WI.knownNat @32
  blkSym <- WI.natLit sym 0
  bv1 <- WI.bvLit sym w32 (BV.mkBV w32 (fromIntegral off1))
  bv2 <- WI.bvLit sym w32 (BV.mkBV w32 (fromIntegral off2))
  cond <- WI.freshConstant sym (WI.safeSymbol "c") CT.BaseBoolRepr
  offSym <- WI.bvIte sym cond bv1 bv2
  let ptr = CLP.LLVMPointer blkSym offSym
  let ptrEntry = mkRegEntry ptr
  extractValidityResult <$>
    mkGlobalPointerValidityPredCommon mutMap immutMap sym puse Nothing ptrEntry

-- | If a write to a concrete block-0 pointer succeeds (pred = True),
-- a read at the same pointer must also succeed.
prop_writeValidImpliesReadValid :: H.Property
prop_writeValidImpliesReadValid =
  H.withTests 10000 $ H.property $ do
    entries <- H.forAll genIntervalEntries
    off <- H.forAll (genOffsetInEntries entries)
    let (mutMap, immutMap) = entriesToSplitMaps entries
    (writeResult, readResult) <- H.evalIO $ withSym $ \sym -> do
      wr <- runValidityPred sym mutMap immutMap off MS.PointerWrite Nothing
      rd <- runValidityPred sym mutMap immutMap off MS.PointerRead Nothing
      pure (wr, rd)
    case (writeResult, readResult) of
      -- Write valid → read must be valid
      (ValidityTrue, ValidityTrue) -> H.success
      (ValidityTrue, _) -> do
        H.footnote "Write was valid but read was not"
        H.failure
      -- Write invalid → read may or may not be valid (immutable region)
      (ValidityFalse, ValidityTrue)  -> H.success
      (ValidityFalse, ValidityFalse) -> H.success
      (ValidityFalse, _) -> do
        H.footnote "Write invalid but read not decidable"
        H.failure
      _ -> H.discard

-- | Write-valid implies read-valid for ite'd pointers: if the write
-- predicate simplifies to True, the read predicate must not simplify
-- to False.
prop_iteWriteValidImpliesReadValid :: H.Property
prop_iteWriteValidImpliesReadValid =
  H.withTests 10000 $ H.property $ do
    entries <- H.forAll genIntervalEntries
    off1 <- H.forAll (genOffsetInEntries entries)
    off2 <- H.forAll (genOffsetInEntries entries)
    let (mutMap, immutMap) = entriesToSplitMaps entries
    (writeResult, readResult) <- H.evalIO $ withSym $ \sym -> do
      wr <- runValidityPredIte sym mutMap immutMap off1 off2 MS.PointerWrite
      rd <- runValidityPredIte sym mutMap immutMap off1 off2 MS.PointerRead
      pure (wr, rd)
    case (writeResult, readResult) of
      -- Write valid → read must not be invalid
      (ValidityTrue, ValidityFalse) -> do
        H.footnote "ite write was valid but ite read was invalid"
        H.failure
      (_, NonGlobalBlock) -> H.discard
      (NonGlobalBlock, _) -> H.discard
      _ -> H.success

-- | For any concrete block-0 pointer and any map, the predicate
-- should always simplify to a constant (True or False).
prop_concreteBlock0Decidable :: H.Property
prop_concreteBlock0Decidable =
  H.withTests 10000 $ H.property $ do
    entries <- H.forAll genIntervalEntries
    off <- H.forAll genOffset
    tag <- H.forAll (Gen.element [MS.PointerRead, MS.PointerWrite])
    let (mutMap, immutMap) = entriesToSplitMaps entries
    result <- H.evalIO $ withSym $ \sym ->
      runValidityPred sym mutMap immutMap off tag Nothing
    case result of
      ValidityTrue  -> H.success
      ValidityFalse -> H.success
      ValiditySymbolic -> do
        H.footnote "Concrete block-0 pointer produced non-trivial predicate"
        H.failure
      NonGlobalBlock -> do
        H.footnote "Concrete block-0 pointer returned NonGlobalBlock"
        H.failure

-- | Any concrete non-zero block returns Nothing regardless of map or offset.
prop_nonZeroBlockNothing :: H.Property
prop_nonZeroBlockNothing =
  H.withTests 10000 $ H.property $ do
    entries <- H.forAll genIntervalEntries
    off <- H.forAll genOffset
    blk <- H.forAll (Gen.integral (Range.linear 1 100))
    tag <- H.forAll (Gen.element [MS.PointerRead, MS.PointerWrite])
    let (mutMap, immutMap) = entriesToSplitMaps entries
    result <- H.evalIO $ withSym $ \sym -> do
      let ?processMacawAssert = defaultProcessMacawAssertion
      let puse = MS.PointerUse Nothing tag
      ptr <- mkPtr sym MC.Addr32 blk (fromIntegral off)
      let ptrEntry = mkRegEntry ptr
      extractValidityResult <$>
        mkGlobalPointerValidityPredCommon mutMap immutMap sym puse Nothing ptrEntry
    result H.=== NonGlobalBlock

-- | A conditional access with a false condition should always produce
-- a trivially true predicate (the access doesn't happen).
prop_falseCondTriviallyTrue :: H.Property
prop_falseCondTriviallyTrue =
  H.withTests 10000 $ H.property $ do
    entries <- H.forAll genIntervalEntries
    off <- H.forAll genOffset
    tag <- H.forAll (Gen.element [MS.PointerRead, MS.PointerWrite])
    let (mutMap, immutMap) = entriesToSplitMaps entries
    result <- H.evalIO $ withSym $ \sym -> do
      let falseCond = CS.RegEntry CT.BoolRepr (WI.falsePred sym)
      runValidityPred sym mutMap immutMap off tag (Just falseCond)
    result H.=== ValidityTrue

-- | For an ite'd pointer (ite c off1 off2), if the validity predicate
-- simplifies to a constant, it must be consistent with both branches.
-- That is, the solver should never claim the ite is valid when a branch
-- is invalid, or vice versa.
prop_itePointerAgreesWhenBranchesAgree :: H.Property
prop_itePointerAgreesWhenBranchesAgree =
  H.withTests 10000 $ H.property $ do
    entries <- H.forAll genIntervalEntries
    off1 <- H.forAll (genOffsetInEntries entries)
    off2 <- H.forAll (genOffsetInEntries entries)
    tag <- H.forAll (Gen.element [MS.PointerRead, MS.PointerWrite])
    let (mutMap, immutMap) = entriesToSplitMaps entries
    (conc1, conc2, iteResult) <- H.evalIO $ withSym $ \sym -> do
      r1 <- runValidityPred sym mutMap immutMap off1 tag Nothing
      r2 <- runValidityPred sym mutMap immutMap off2 tag Nothing
      ri <- runValidityPredIte sym mutMap immutMap off1 off2 tag
      pure (r1, r2, ri)
    -- If the ite result simplifies, it must be consistent with branches.
    case (conc1, conc2, iteResult) of
      -- If ite simplifies to True, both branches must be True
      (ValidityTrue, ValidityTrue, ValidityTrue) -> H.success
      (_, _, ValidityTrue) -> do
        H.footnote "ite simplified to True but not both branches are True"
        H.failure
      -- If ite simplifies to False, both branches must be False
      (ValidityFalse, ValidityFalse, ValidityFalse) -> H.success
      (_, _, ValidityFalse) -> do
        H.footnote "ite simplified to False but not both branches are False"
        H.failure
      -- Non-trivial ite result is always acceptable
      (_, _, ValiditySymbolic) -> H.success
      _ -> H.discard
