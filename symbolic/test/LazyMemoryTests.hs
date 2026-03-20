{-# LANGUAGE ScopedTypeVariables #-}
module LazyMemoryTests (tests) where

import           Data.Word ( Word64 )
import qualified Data.ByteString as BS
import qualified Data.IntervalMap.Interval as IMI

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import           Test.Tasty ( TestTree, testGroup )
import           Test.Tasty.Hedgehog

import           Data.Macaw.Symbolic.Memory.Lazy ( slicePlan )

tests :: TestTree
tests = testGroup "slicePlan"
  [ testProperty "single chunk, read fits inside" prop_singleChunkFits
  , testProperty "empty input returns Nothing" prop_emptyInput
  , testProperty "insufficient coverage returns Nothing" prop_insufficientCoverage
  , testProperty "non-contiguous chunks returns Nothing" prop_nonContiguous
  , testProperty "multi-chunk spanning read" prop_multiChunkSpan
  , testProperty "sum of takes equals numBytes" prop_sumTakes
  , testProperty "offsets are within bounds" prop_offsetsInBounds
  , testProperty "round-trip with reference" prop_roundTrip
  ]

-- | Generate a single IntervalCO interval containing the given read window.
prop_singleChunkFits :: H.Property
prop_singleChunkFits = H.property $ do
  lo <- H.forAll $ Gen.word64 Range.linearBounded
  -- Keep addr - lo within Int range (slicePlan uses fromIntegral @a @Int)
  let maxSkip = min (fromIntegral (maxBound :: Int)) (maxBound - lo)
  addr <- H.forAll $ Gen.word64 (Range.linear lo (lo + maxSkip))
  n <- H.forAll $ Gen.int (Range.linear 1 (fromIntegral (min 100 (maxBound - addr - 1))))
  let hi = addr + fromIntegral n + 1
      interval = IMI.IntervalCO lo hi
      expected = Just [(fromIntegral (addr - lo), n)]
  slicePlan addr n [interval] H.=== expected

-- | Empty interval list always returns Nothing.
prop_emptyInput :: H.Property
prop_emptyInput = H.property $ do
  addr <- H.forAll $ Gen.word64 Range.linearBounded
  n <- H.forAll $ Gen.int (Range.linear 1 100)
  slicePlan addr n ([] :: [IMI.Interval Word64]) H.=== Nothing

-- | Read extending past the last chunk returns Nothing.
prop_insufficientCoverage :: H.Property
prop_insufficientCoverage = H.property $ do
  lo <- H.forAll $ Gen.word64 (Range.linear 0 (maxBound - 100))
  chunkLen <- H.forAll $ Gen.word64 (Range.linear 1 (min 100 (maxBound - lo)))
  let hi = lo + chunkLen
      addr = lo
  -- Read more bytes than the chunk covers
  n <- H.forAll $ Gen.int (Range.linear (fromIntegral chunkLen + 1) (fromIntegral chunkLen + 100))
  slicePlan addr n [IMI.IntervalCO lo hi] H.=== Nothing

-- | Gap between intervals returns Nothing.
prop_nonContiguous :: H.Property
prop_nonContiguous = H.property $ do
  lo1 <- H.forAll $ Gen.word64 (Range.linear 0 (maxBound - 300))
  len1 <- H.forAll $ Gen.word64 (Range.linear 1 100)
  gap <- H.forAll $ Gen.word64 (Range.linear 1 100)
  len2 <- H.forAll $ Gen.word64 (Range.linear 1 100)
  let hi1 = lo1 + len1
      lo2 = hi1 + gap
      hi2 = lo2 + len2
      totalLen = len1 + gap + len2
      n = fromIntegral totalLen
  slicePlan lo1 n [IMI.IntervalCO lo1 hi1, IMI.IntervalCO lo2 hi2] H.=== Nothing

-- | Two contiguous chunks that together cover the read.
prop_multiChunkSpan :: H.Property
prop_multiChunkSpan = H.property $ do
  lo <- H.forAll $ Gen.word64 (Range.linear 0 (maxBound - 200))
  len1 <- H.forAll $ Gen.word64 (Range.linear 1 100)
  len2 <- H.forAll $ Gen.word64 (Range.linear 1 100)
  let mid = lo + len1
      hi = mid + len2
      n = fromIntegral (len1 + len2)
      intervals = [IMI.IntervalCO lo mid, IMI.IntervalCO mid hi]
      expected = Just [(0, fromIntegral len1), (0, fromIntegral len2)]
  slicePlan lo n intervals H.=== expected

-- | For any Just result, the sum of takes equals numBytes.
prop_sumTakes :: H.Property
prop_sumTakes = H.property $ do
  (addr, n, intervals) <- H.forAll genCoveringIntervals
  case slicePlan addr n intervals of
    Nothing -> H.success
    Just plan -> sum (map snd plan) H.=== n

-- | For any Just result, each (skip, take) is within chunk bounds.
prop_offsetsInBounds :: H.Property
prop_offsetsInBounds = H.property $ do
  (addr, n, intervals) <- H.forAll genCoveringIntervals
  case slicePlan addr n intervals of
    Nothing -> H.success
    Just plan -> do
      let chunkLens = map (\(IMI.IntervalCO lo hi) -> fromIntegral (hi - lo)
                              :: Int) intervals
      mapM_ (\((skip, take_), chunkLen) -> do
        H.assert (skip >= 0)
        H.assert (take_ > 0)
        H.assert (skip + take_ <= chunkLen)
        ) (zip plan chunkLens)

-- | Generate a flat ByteString, chunk it into contiguous intervals, pick a
-- random read window, verify slicePlan produces slices that reconstruct the
-- correct sub-range.
prop_roundTrip :: H.Property
prop_roundTrip = H.property $ do
  totalBytes <- H.forAll $ Gen.bytes (Range.linear 1 500)
  let totalLen = BS.length totalBytes
  -- Generate internal chunk boundaries (numChunks-1 cuts for numChunks chunks)
  numChunks <- H.forAll $ Gen.int (Range.linear 1 (min 10 totalLen))
  internalCuts <- genSortedUnique (numChunks - 1) 1 (totalLen - 1)
  let cuts' = [0] ++ internalCuts ++ [totalLen]
      intervals =
        [ IMI.IntervalCO (fromIntegral lo :: Word64) (fromIntegral hi)
        | (lo, hi) <- zip cuts' (tail cuts')
        , lo < hi
        ]
      chunks =
        [ BS.take (hi - lo) (BS.drop lo totalBytes)
        | (lo, hi) <- zip cuts' (tail cuts')
        , lo < hi
        ]
  -- Pick a random read window within [0, totalLen)
  readStart <- H.forAll $ Gen.int (Range.linear 0 (totalLen - 1))
  readLen <- H.forAll $ Gen.int (Range.linear 1 (totalLen - readStart))
  let addr = fromIntegral readStart :: Word64
      readEnd = addr + fromIntegral readLen
      -- Filter to intervals that actually intersect [addr, addr+readLen),
      -- mirroring what IM.intersecting does in real usage.
      overlaps (IMI.IntervalCO lo hi) = lo < readEnd && hi > addr
      overlaps _ = False
      relevantPairs = filter (\(i, _) -> overlaps i) (zip intervals chunks)
      relevantIntervals = map fst relevantPairs
      relevantChunks = map snd relevantPairs
  case slicePlan addr readLen relevantIntervals of
    Nothing -> do
      H.annotate "slicePlan returned Nothing for a contiguous covering set"
      H.failure
    Just plan -> do
      let reconstructed = BS.concat
            [ BS.take t (BS.drop s c)
            | ((s, t), c) <- zip plan relevantChunks
            ]
          expected = BS.take readLen (BS.drop readStart totalBytes)
      reconstructed H.=== expected

-- | Generate sorted unique Ints in a range, for use as chunk boundaries.
genSortedUnique :: Monad m => Int -> Int -> Int -> H.PropertyT m [Int]
genSortedUnique count lo hi
  | count <= 0 || lo > hi = pure []
  | otherwise = do
      vals <- H.forAll $ Gen.list (Range.singleton count)
                (Gen.int (Range.linear lo hi))
      let sorted = take count $ dedup $ sort' vals
      pure sorted
  where
    sort' [] = []
    sort' (x:xs) = sort' [y | y <- xs, y < x] ++ [x] ++ sort' [y | y <- xs, y >= x]
    dedup [] = []
    dedup [x] = [x]
    dedup (x:y:rest)
      | x == y    = dedup (y:rest)
      | otherwise = x : dedup (y:rest)

-- | Generate intervals that form a contiguous covering set (may or may not
-- cover a given read).
genCoveringIntervals :: H.Gen (Word64, Int, [IMI.Interval Word64])
genCoveringIntervals = do
  base <- Gen.word64 (Range.linear 0 (maxBound - 500))
  numChunks <- Gen.int (Range.linear 1 5)
  chunkLens <- Gen.list (Range.singleton numChunks)
                 (Gen.word64 (Range.linear 1 100))
  let boundaries = scanl (+) base chunkLens
      intervals = zipWith IMI.IntervalCO boundaries (tail boundaries)
      totalLen = sum (map fromIntegral chunkLens :: [Int])
  -- Pick a read that starts somewhere in the first chunk
  addr <- Gen.word64 (Range.linear base (base + head chunkLens - 1))
  let maxRead = totalLen - fromIntegral (addr - base)
  n <- Gen.int (Range.linear 1 (max 1 maxRead))
  pure (addr, n, intervals)
