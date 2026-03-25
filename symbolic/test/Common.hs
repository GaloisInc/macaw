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
                   ( mkGlobalPointerValidityPredCommon
                   , defaultProcessMacawAssertion
                   )
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.LLVM.MemModel.Pointer as CLP
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import           Data.Parameterized.Nonce (newIONonceGenerator)
import           Data.Parameterized.Some (Some(..))
import qualified What4.Expr as WE
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import           What4.LabeledPred (LabeledPred(..))

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.HUnit ((@?=), testCase)
import           Test.Tasty.Hedgehog (testPropertyNamed)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- | Set up a What4 expression builder for tests.
withSym :: (forall t. WEB.ExprBuilder t WE.EmptyExprBuilderState (WEB.Flags WEB.FloatIEEE) -> IO a) -> IO a
withSym f = do
  Some ng <- newIONonceGenerator
  sym <- WEB.newExprBuilder WEB.FloatIEEERepr WE.EmptyExprBuilderState ng
  f sym

-- | Build an LLVMPointer from a concrete block number and offset.
mkPtr ::
  WI.IsExprBuilder sym =>
  sym ->
  MC.AddrWidthRepr w ->
  Natural ->
  Word64 ->
  IO (CL.LLVMPtr sym w)
mkPtr sym repr blk off = do
  blkSym <- WI.natLit sym blk
  offSym <- case repr of
    MC.Addr32 -> WI.bvLit sym (WI.knownNat @32)
                   (BV.mkBV (WI.knownNat @32) (fromIntegral @Word64 @Integer off))
    MC.Addr64 -> WI.bvLit sym (WI.knownNat @64) (BV.word64 off)
  pure (CLP.LLVMPointer blkSym offSym)

-- | Wrap an LLVMPointer in a RegEntry.
mkRegEntry :: (1 <= w, KnownNat w) => CL.LLVMPtr sym w -> CS.RegEntry sym (CL.LLVMPointerType w)
mkRegEntry ptr = CS.RegEntry (CL.LLVMPointerRepr WI.knownNat) ptr

-- | Split (lo, hi, mutability) triples into separate mutable and immutable
-- IntervalMaps, matching the split-map API of mkGlobalPointerValidityPredCommon.
mkSplitMaps ::
  forall w.
  MC.MemWidth w =>
  [(Word64, Word64, CL.Mutability)] ->
  ( IM.IntervalMap (MC.MemWord w) ()
  , IM.IntervalMap (MC.MemWord w) ()
  )
mkSplitMaps entries =
  ( IM.fromList [ (iv, ()) | (lo, hi, CL.Mutable)   <- entries
                            , let iv = IMI.IntervalCO (fromIntegral lo) (fromIntegral hi) ]
  , IM.fromList [ (iv, ()) | (lo, hi, CL.Immutable) <- entries
                            , let iv = IMI.IntervalCO (fromIntegral lo) (fromIntegral hi) ]
  )

-- | Parameterized test for mkGlobalPointerValidityPredCommon.
--
-- Expected result encoding:
--   Nothing          → function should return Nothing (non-global block)
--   Just Nothing     → function returns Just, but predicate is non-trivial (symbolic)
--   Just (Just True) → function returns Just, predicate simplifies to True
--   Just (Just False)→ function returns Just, predicate simplifies to False
testValidityPred ::
  String ->
  [(Word64, Word64, CL.Mutability)] ->
  Natural ->
  Word64 ->
  MS.PointerUseTag ->
  Maybe Bool ->
  Maybe (Maybe Bool) ->
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
      res <- mkGlobalPointerValidityPredCommon mutMap immutMap sym puse mcondEntry ptrEntry
      pure $ case res of
        Nothing -> Nothing
        Just (LabeledPred p _) -> Just (WI.asConstantPred p)
    result @?= expected

-- | Like testValidityPred but for a symbolic block ID.
testValidityPredSymbolicBlock ::
  String ->
  [(Word64, Word64, CL.Mutability)] ->
  Word64 ->
  MS.PointerUseTag ->
  Maybe (Maybe Bool) ->
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
      res <- mkGlobalPointerValidityPredCommon mutMap immutMap sym puse Nothing ptrEntry
      pure $ case res of
        Nothing -> Nothing
        Just (LabeledPred p _) -> Just (WI.asConstantPred p)
    result @?= expected

-- | Test with a symbolic offset that is an ite of two concrete values.
-- The pointer has block 0 and offset @ite freshBool off1 off2@.
testValidityPredIteOffset ::
  String ->
  [(Word64, Word64, CL.Mutability)] ->
  Word64 ->
  Word64 ->
  MS.PointerUseTag ->
  Maybe (Maybe Bool) ->
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
      res <- mkGlobalPointerValidityPredCommon mutMap immutMap sym puse Nothing ptrEntry
      pure $ case res of
        Nothing -> Nothing
        Just (LabeledPred p _) -> Just (WI.asConstantPred p)
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
              (Just (Just True))
          , testValidityPred
              "Read from immutable region"
              [(100, 200, CL.Immutable)]
              0
              150
              MS.PointerRead
              Nothing
              (Just (Just True))
          , testValidityPred
              "Write to mutable region"
              [(100, 200, CL.Mutable)]
              0
              150
              MS.PointerWrite
              Nothing
              (Just (Just True))
          , testValidityPred
              "Write to immutable region (rejected)"
              [(100, 200, CL.Immutable)]
              0
              150
              MS.PointerWrite
              Nothing
              (Just (Just False))
          ]
      , testGroup "Unmapped access"
          [ testValidityPred
              "Read from unmapped region"
              [(100, 200, CL.Mutable)]
              0
              300
              MS.PointerRead
              Nothing
              (Just (Just False))
          , testValidityPred
              "Write to unmapped region"
              [(100, 200, CL.Mutable)]
              0
              300
              MS.PointerWrite
              Nothing
              (Just (Just False))
          , testValidityPred
              "Empty map"
              []
              0
              100
              MS.PointerRead
              Nothing
              (Just (Just False))
          ]
      , testGroup "Block ID"
          [ testValidityPred
              "Non-zero block returns Nothing"
              [(100, 200, CL.Mutable)]
              1
              150
              MS.PointerRead
              Nothing
              Nothing
          , testValidityPredSymbolicBlock
              "Symbolic block, in-range offset simplifies to True"
              [(100, 200, CL.Mutable)]
              150
              MS.PointerRead
              (Just (Just True))  -- ite (blk==0) True True = True
          , testValidityPredSymbolicBlock
              "Symbolic block, out-of-range offset is non-trivial"
              [(100, 200, CL.Mutable)]
              300
              MS.PointerRead
              (Just Nothing)  -- ite (blk==0) False True — not simplifiable
          ]
      , testGroup "Boundary conditions"
          [ testValidityPred
              "At lower bound (inclusive)"
              [(100, 200, CL.Mutable)]
              0
              100
              MS.PointerRead
              Nothing
              (Just (Just True))
          , testValidityPred
              "At upper bound (exclusive)"
              [(100, 200, CL.Mutable)]
              0
              200
              MS.PointerRead
              Nothing
              (Just (Just False))
          ]
      , testGroup "Conditional writes"
          [ testValidityPred
              "Conditional write with false condition is trivially true"
              [(100, 200, CL.Immutable)]
              0
              150
              MS.PointerWrite
              (Just False)
              (Just (Just True))
          ]
      , testGroup "Symbolic offsets (ite of two concrete values)"
          [ testValidityPredIteOffset
              "Both branches in range"
              [(100, 200, CL.Mutable)]
              150  -- in range
              160  -- in range
              MS.PointerRead
              (Just (Just True))
          , testValidityPredIteOffset
              "Both branches out of range"
              [(100, 200, CL.Mutable)]
              50   -- out of range
              300  -- out of range
              MS.PointerRead
              (Just Nothing)  -- non-trivial (What4 can't simplify through range checks)
          , testValidityPredIteOffset
              "One branch in range, one out"
              [(100, 200, CL.Mutable)]
              150  -- in range
              300  -- out of range
              MS.PointerRead
              (Just Nothing)  -- non-trivial
          , testValidityPredIteOffset
              "Write with one branch in mutable, one in immutable"
              [(100, 200, CL.Mutable), (300, 400, CL.Immutable)]
              150  -- in mutable (write OK)
              350  -- in immutable (write rejected)
              MS.PointerWrite
              (Just Nothing)  -- non-trivial
          , testValidityPredIteOffset
              "Read with one branch in mutable, one in immutable"
              [(100, 200, CL.Mutable), (300, 400, CL.Immutable)]
              150  -- in mutable
              350  -- in immutable
              MS.PointerRead
              (Just Nothing)  -- non-trivial (What4 can't simplify through range checks)
          , testValidityPredIteOffset
              "Branches straddle lower bound"
              [(100, 200, CL.Mutable)]
              99   -- just below
              100  -- at bound (inclusive)
              MS.PointerRead
              (Just Nothing)  -- non-trivial
          , testValidityPredIteOffset
              "Branches straddle upper bound"
              [(100, 200, CL.Mutable)]
              199  -- in range
              200  -- at bound (exclusive, out of range)
              MS.PointerRead
              (Just Nothing)  -- non-trivial
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
  ( IM.IntervalMap (MC.MemWord 32) ()
  , IM.IntervalMap (MC.MemWord 32) ()
  )
entriesToSplitMaps entries =
  ( IM.fromList [ (iv, ()) | e <- entries, ieMut e == CL.Mutable
                            , let iv = IMI.IntervalCO (fromIntegral (ieLo e)) (fromIntegral (ieHi e)) ]
  , IM.fromList [ (iv, ()) | e <- entries, ieMut e == CL.Immutable
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
  IM.IntervalMap (MC.MemWord 32) () ->
  IM.IntervalMap (MC.MemWord 32) () ->
  Word32 ->
  MS.PointerUseTag ->
  Maybe (CS.RegEntry (WEB.ExprBuilder t WE.EmptyExprBuilderState (WEB.Flags WEB.FloatIEEE)) CT.BoolType) ->
  IO (Maybe (Maybe Bool))
runValidityPred sym mutMap immutMap off tag mcondEntry = do
  let ?processMacawAssert = defaultProcessMacawAssertion
  let puse = MS.PointerUse Nothing tag
  ptr <- mkPtr sym MC.Addr32 0 (fromIntegral off)
  let ptrEntry = mkRegEntry ptr
  res <- mkGlobalPointerValidityPredCommon mutMap immutMap sym puse mcondEntry ptrEntry
  pure $ case res of
    Nothing -> Nothing
    Just (LabeledPred p _) -> Just (WI.asConstantPred p)

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
  IM.IntervalMap (MC.MemWord 32) () ->
  IM.IntervalMap (MC.MemWord 32) () ->
  Word32 ->
  Word32 ->
  MS.PointerUseTag ->
  IO (Maybe (Maybe Bool))
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
  res <- mkGlobalPointerValidityPredCommon mutMap immutMap sym puse Nothing ptrEntry
  pure $ case res of
    Nothing -> Nothing
    Just (LabeledPred p _) -> Just (WI.asConstantPred p)

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
      (Just (Just True), Just (Just True)) -> H.success
      (Just (Just True), _) -> do
        H.footnote "Write was valid but read was not"
        H.failure
      -- Write invalid → read may or may not be valid (immutable region)
      (Just (Just False), Just (Just _)) -> H.success
      (Just (Just False), _) -> do
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
      (Just (Just True), Just (Just False)) -> do
        H.footnote "ite write was valid but ite read was invalid"
        H.failure
      (Just _, Just _) -> H.success
      _ -> H.discard

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
      Just (Just _) -> H.success
      Just Nothing -> do
        H.footnote "Concrete block-0 pointer produced non-trivial predicate"
        H.failure
      Nothing -> do
        H.footnote "Concrete block-0 pointer returned Nothing"
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
      res <- mkGlobalPointerValidityPredCommon mutMap immutMap sym puse Nothing ptrEntry
      pure $ case res of
        Nothing -> Nothing
        Just (LabeledPred p _) -> Just (WI.asConstantPred p)
    result H.=== Nothing

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
    result H.=== Just (Just True)

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
      (Just (Just True), Just (Just True), Just (Just True)) -> H.success
      (_, _, Just (Just True)) -> do
        H.footnote "ite simplified to True but not both branches are True"
        H.failure
      -- If ite simplifies to False, both branches must be False
      (Just (Just False), Just (Just False), Just (Just False)) -> H.success
      (_, _, Just (Just False)) -> do
        H.footnote "ite simplified to False but not both branches are False"
        H.failure
      -- Non-trivial ite result is always acceptable
      (_, _, Just Nothing) -> H.success
      _ -> H.discard
