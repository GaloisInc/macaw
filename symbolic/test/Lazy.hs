{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Lazy (tests) where

import           Data.Bits (shiftR, (.&.))
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.Vector as Vec
import qualified Data.IntervalMap.Strict as IM
import qualified Data.IntervalMap.Interval as IMI
import qualified Data.IntervalSet as IS
import           Data.Maybe (isJust, isNothing)
import           Data.Word (Word8, Word32, Word64)
import           Numeric.Natural (Natural)

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Symbolic as MS
import           Data.Macaw.Types (BVType)
import           Data.Macaw.Symbolic.Memory.Common
                   ( MemoryModelContents(..)
                   , MutableIntervalMap(..)
                   , ImmutableIntervalMap(..)
                   , mkGlobalPointerValidityPredCommon
                   , defaultProcessMacawAssertion
                   )
import           Data.Macaw.Symbolic.Memory.Lazy.Internal
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.LLVM.MemModel.Pointer as CLP
import qualified Lang.Crucible.Simulator as CS
import qualified What4.Interface as WI

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.Hedgehog (testPropertyNamed)
import           Test.Tasty.HUnit ((@?=), assertBool, testCase)

import           Utils (withSym, mkPtr)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- | Safe widening from 'Word32' to 'Word64'.
word32ToWord64 :: Word32 -> Word64
word32ToWord64 = fromIntegral @Word32 @Word64

-- | Checked narrowing into a 'MC.MemWord'. Calls 'error' if the value
-- doesn't fit (i.e., when @w ~ 32@ and the value exceeds 'maxBound').
checkedToMemWord ::
  forall w. MC.MemWidth w => Word64 -> MC.MemWord w
checkedToMemWord x
  | result' == x = result
  | otherwise    = error $
      "checkedToMemWord: " ++ show x ++ " out of range for MemWord"
  where
    result  = fromIntegral @Word64 @(MC.MemWord w) x
    result' = fromIntegral @(MC.MemWord w) @Word64 result

-- | Global memory block number used in tests.
globalBlock :: Natural
globalBlock = 1

-- | Build an LLVMPointer in the global block with the given offset.
mkGlobalPtr ::
  WI.IsExprBuilder sym =>
  sym ->
  MC.AddrWidthRepr w ->
  Word64 ->
  IO (CL.LLVMPtr sym w)
mkGlobalPtr sym repr off = mkPtr sym repr globalBlock off

-- | 1-byte BVMemRepr (little-endian)
bv1 :: MC.MemRepr (BVType 8)
bv1 = MC.BVMemRepr (WI.knownNat @1) MC.LittleEndian

-- | 2-byte BVMemRepr (little-endian)
bv2 :: MC.MemRepr (BVType 16)
bv2 = MC.BVMemRepr (WI.knownNat @2) MC.LittleEndian

-- | 4-byte BVMemRepr (little-endian)
bv4 :: MC.MemRepr (BVType 32)
bv4 = MC.BVMemRepr (WI.knownNat @4) MC.LittleEndian

-- | 8-byte BVMemRepr (little-endian)
bv8 :: MC.MemRepr (BVType 64)
bv8 = MC.BVMemRepr (WI.knownNat @8) MC.LittleEndian

-- | 16-byte BVMemRepr (little-endian)
bv16 :: MC.MemRepr (BVType 128)
bv16 = MC.BVMemRepr (WI.knownNat @16) MC.LittleEndian

-- | 32-byte BVMemRepr (little-endian)
bv32 :: MC.MemRepr (BVType 256)
bv32 = MC.BVMemRepr (WI.knownNat @32) MC.LittleEndian

-- | Existential wrapper for a BVMemRepr with some width.
data SomeBVMemRepr where
  SomeBVMemRepr :: (1 WI.<= w) => MC.MemRepr (BVType w) -> SomeBVMemRepr

-- | Get the appropriate MemRepr for a given size in bytes.
bvMemReprForSize :: Int -> Maybe SomeBVMemRepr
bvMemReprForSize = \case
  1  -> Just (SomeBVMemRepr bv1)
  2  -> Just (SomeBVMemRepr bv2)
  4  -> Just (SomeBVMemRepr bv4)
  8  -> Just (SomeBVMemRepr bv8)
  16 -> Just (SomeBVMemRepr bv16)
  32 -> Just (SomeBVMemRepr bv32)
  _  -> Nothing

-- | Build a SymbolicMemChunk from concrete bytes.
mkChunk ::
  [Word8] ->
  SymbolicMemChunk sym
mkChunk bytes = ConcreteBytes (BS.pack bytes)

-- | Build a SymbolicBytes chunk from concrete byte values.
-- Unlike 'mkChunk', this uses the 'SymbolicBytes' constructor
-- (backed by a Vector of symbolic BV literals).
mkSymbolicChunk ::
  WI.IsExprBuilder sym =>
  sym ->
  [Word8] ->
  IO (SymbolicMemChunk sym)
mkSymbolicChunk sym bytes = do
  symBytes <- traverse (\b -> WI.bvLit sym (WI.knownNat @8) (BV.mkBV (WI.knownNat @8) (fromIntegral b))) bytes
  pure $ SymbolicBytes (Vec.fromList symBytes)

-- | Build an IntervalMap from a list of (base, chunk) pairs.
-- Uses IntervalCO (closed-open) intervals.
mkIntervalMap ::
  forall w sym.
  MC.MemWidth w =>
  [(Word64, SymbolicMemChunk sym)] ->
  IM.IntervalMap (MC.MemWord w) (SymbolicMemChunk sym)
mkIntervalMap entries = IM.fromList
  [ ( IMI.IntervalCO
        (checkedToMemWord @w lo)
        (checkedToMemWord @w lo + checkedToMemWord @w len)
    , c )
  | (lo, c) <- entries
  , let len = fromIntegral @Int @Word64 (symChunkLen c)
  ]

-- | Helper to test an immutable read operation and verify the result.
-- Creates an interval map from the provided concrete and symbolic chunks,
-- performs the read, and checks the result.
testImmutableRead ::
  MC.MemWidth w =>
  MC.AddrWidthRepr w ->
  String ->                 -- ^ Test name
  [(Word64, [Word8])] ->    -- ^ Concrete memory chunks (base address, bytes)
  [(Word64, [Word8])] ->    -- ^ Symbolic memory chunks (base address, bytes)
  Word64 ->                 -- ^ Read address
  MC.MemRepr (BVType w') -> -- ^ Read size/type
  Maybe [Word8] ->          -- ^ Expected result (Nothing = should fail)
  TestTree
testImmutableRead repr name concreteChunks symbolicChunks readAddr memRepr expected = testCase name $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    symChunks <- traverse (\(base, bytes) -> fmap (\c -> (base, c)) (mkSymbolicChunk sym bytes)) symbolicChunks
    let allChunks = [(base, mkChunk bytes) | (base, bytes) <- concreteChunks] ++ symChunks
    let imap = mkIntervalMap allChunks
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym repr readAddr
    let mutMap = MutableIntervalMap (mkIntervalMap [])
        immutMap = ImmutableIntervalMap imap
    res <- concreteUnmutatedGlobalReadWithPopulatedChunks sym mutMap immutMap cache globalBlk ConcreteMutable IS.empty memRepr ptr
    pure $ case res of
      Nothing -> Nothing
      Just val -> extractLEBytes val (fromIntegral $ MC.memReprBytes memRepr)
  result @?= expected


------------------------------------------------------------------------
-- Unit tests
------------------------------------------------------------------------

read1 :: TestTree
read1 = testImmutableRead MC.Addr32
  "One-byte read"
  [(100, [0xAA, 0xBB])]
  []
  100
  bv1
  (Just [0xAA])

read2 :: TestTree
read2 = testImmutableRead MC.Addr32
  "Two-byte read"
  [(100, [0xAA, 0xBB, 0xCC])]
  []
  100
  bv2
  (Just [0xAA, 0xBB])

read4 :: TestTree
read4 = testImmutableRead MC.Addr32
  "Four-byte read"
  [(200, [0x11, 0x22, 0x33, 0x44, 0x55])]
  []
  200
  bv4
  (Just [0x11, 0x22, 0x33, 0x44])

readFromOffset :: TestTree
readFromOffset = testImmutableRead MC.Addr32
  "Read from offset within chunk"
  [(300, [0x10, 0x20, 0x30, 0x40, 0x50])]
  []
  302  -- offset 2 into the chunk
  bv2
  (Just [0x30, 0x40])

-- | Read from an offset within a SymbolicBytes chunk (as opposed to
-- ConcreteBytes).
readFromOffsetSymbolicBytes :: TestTree
readFromOffsetSymbolicBytes = testImmutableRead MC.Addr32
  "Read from offset within SymbolicBytes chunk"
  []
  [(100, [0x10, 0x20, 0x30, 0x40])]
  101  -- offset 1 into the chunk
  bv2
  (Just [0x20, 0x30])

-- | Read an entire SymbolicBytes chunk.
readFullSymbolicBytes :: TestTree
readFullSymbolicBytes = testImmutableRead MC.Addr32
  "Full read of SymbolicBytes chunk"
  []
  [(100, [0xAA, 0xBB])]
  100
  bv2
  (Just [0xAA, 0xBB])

-- | Read spanning two contiguous SymbolicBytes chunks.
readSpanningSymbolicBytes :: TestTree
readSpanningSymbolicBytes = testImmutableRead MC.Addr32
  "Read spanning contiguous SymbolicBytes chunks"
  []
  [(100, [0xAA, 0xBB]), (102, [0xCC, 0xDD])]
  101  -- spans boundary between chunks
  bv2
  (Just [0xBB, 0xCC])

-- | Read spanning a ConcreteBytes chunk into a SymbolicBytes chunk.
readSpanningConcreteIntoSymbolic :: TestTree
readSpanningConcreteIntoSymbolic = testImmutableRead MC.Addr32
  "Read spanning ConcreteBytes into SymbolicBytes"
  [(100, [0x11, 0x22])]
  [(102, [0x33, 0x44])]
  101
  bv2
  (Just [0x22, 0x33])

readSpanningContiguousChunks :: TestTree
readSpanningContiguousChunks = testImmutableRead MC.Addr32
  "Read spanning contiguous chunks"
  [(100, [0xAA, 0xBB]), (102, [0xCC, 0xDD])]
  []
  101  -- start in first chunk, span into second
  bv2
  (Just [0xBB, 0xCC])

read8 :: TestTree
read8 = testImmutableRead MC.Addr32
  "Eight-byte read"
  [(1000, [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09])]
  []
  1000
  bv8
  (Just [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08])

readFromAddressZero :: TestTree
readFromAddressZero = testImmutableRead MC.Addr32
  "Read from address zero"
  [(0, [0xFF, 0xFE, 0xFD, 0xFC])]
  []
  0
  bv4
  (Just [0xFF, 0xFE, 0xFD, 0xFC])

readAtChunkBoundary :: TestTree
readAtChunkBoundary = testImmutableRead MC.Addr32
  "Read ending exactly at chunk boundary"
  [(100, [0xAA, 0xBB, 0xCC, 0xDD])]
  []
  100
  bv4
  (Just [0xAA, 0xBB, 0xCC, 0xDD])

readLastByteOfChunk :: TestTree
readLastByteOfChunk = testImmutableRead MC.Addr32
  "Read last byte of chunk"
  [(100, [0xAA, 0xBB, 0xCC])]
  []
  102
  bv1
  (Just [0xCC])

readNearMaxBound :: TestTree
readNearMaxBound = testImmutableRead MC.Addr32
  "Read from near maxBound"
  [(w32Max - 10, [0x01, 0x02, 0x03, 0x04, 0x05])]
  []
  (w32Max - 10)
  bv4
  (Just [0x01, 0x02, 0x03, 0x04])

-- | maxBound for Word32, as a Word64
w32Max :: Word64
w32Max = fromIntegral (maxBound :: Word32)

wrongBlockReturnsNothing :: TestTree
wrongBlockReturnsNothing = testCase "Wrong block returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let chunk = mkChunk [0xAA, 0xBB]
    let imap = mkIntervalMap @32 [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkPtr sym MC.Addr32 2 100  -- block 2, but global is block 1
    let mm = MutableIntervalMap (mkIntervalMap [])
        im = ImmutableIntervalMap imap
    r <- concreteUnmutatedGlobalReadWithPopulatedChunks sym mm im cache globalBlk ConcreteMutable IS.empty bv1 ptr
    pure (isNothing r)
  assertBool "wrong block should return Nothing" result

symbolicOffsetReturnsNothing :: TestTree
symbolicOffsetReturnsNothing = testCase "Symbolic offset returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let chunk = mkChunk [0xAA, 0xBB]
    let imap = mkIntervalMap @32 [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    blkSym <- WI.natLit sym globalBlock
    offSym <- WI.freshConstant sym (WI.safeSymbol "off") (WI.BaseBVRepr (WI.knownNat @32))
    let ptr = CLP.LLVMPointer blkSym offSym
    let mm = MutableIntervalMap (mkIntervalMap [])
        im = ImmutableIntervalMap imap
    r <- concreteUnmutatedGlobalReadWithPopulatedChunks sym mm im cache globalBlk ConcreteMutable IS.empty bv1 ptr
    pure (isNothing r)
  assertBool "symbolic offset should return Nothing" result

unpopulatedMutableRegionReturnsJust :: TestTree
unpopulatedMutableRegionReturnsJust = testCase "Unpopulated mutable region returns concrete bytes" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    -- The conc-reads optimization allows reading from unpopulated mutable regions
    let chunk = mkChunk [0xAA, 0xBB]
    let mutMap = mkIntervalMap @32 [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym MC.Addr32 100
    let mm = MutableIntervalMap mutMap
        im = ImmutableIntervalMap (mkIntervalMap [])
    r <- concreteUnmutatedGlobalReadWithPopulatedChunks sym mm im cache globalBlk ConcreteMutable IS.empty bv1 ptr
    pure $ case r of
      Nothing -> Nothing
      Just val -> extractLEBytes val 1
  result @?= Just [0xAA]

populatedMutableRegionReturnsNothing :: TestTree
populatedMutableRegionReturnsNothing = testCase "Populated mutable region returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let chunk = mkChunk [0xAA, 0xBB]
    let mutMap = mkIntervalMap @32 [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym MC.Addr32 100
    -- Mark the chunk as populated
    let populated = IS.singleton (IMI.IntervalCO 100 102)
    let mm = MutableIntervalMap mutMap
        im = ImmutableIntervalMap (mkIntervalMap [])
    r <- concreteUnmutatedGlobalReadWithPopulatedChunks sym mm im cache globalBlk ConcreteMutable populated bv1 ptr
    pure (isNothing r)
  assertBool "populated mutable region should return Nothing" result

symbolicMutableUnpopulatedReturnsNothing :: TestTree
symbolicMutableUnpopulatedReturnsNothing = testCase "SymbolicMutable: unpopulated mutable region returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let chunk = mkChunk [0xAA, 0xBB]
    let imap = mkIntervalMap @32 [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym MC.Addr32 100
    let mm = MutableIntervalMap imap
        im = ImmutableIntervalMap (mkIntervalMap [])
    r <- concreteUnmutatedGlobalReadWithPopulatedChunks sym mm im cache globalBlk SymbolicMutable IS.empty bv1 ptr
    pure (isNothing r)
  assertBool "SymbolicMutable mutable region should return Nothing even when unpopulated" result

notEnoughBytesReturnsNothing :: TestTree
notEnoughBytesReturnsNothing = testImmutableRead MC.Addr32
  "Not enough bytes returns Nothing"
  [(100, [0xAA, 0xBB])]
  []
  100
  bv4
  Nothing

nonContiguousRegionsReturnsNothing :: TestTree
nonContiguousRegionsReturnsNothing = testCase "Non-contiguous regions returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let chunk1 = mkChunk [0xAA]
    let chunk2 = mkChunk [0xBB]
    let imap = IM.fromList
          [ (IMI.IntervalCO (100 :: MC.MemWord 32) 101, chunk1)
          , (IMI.IntervalCO 102 103, chunk2)
          ]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym MC.Addr32 100
    let mm = MutableIntervalMap (mkIntervalMap [])
        im = ImmutableIntervalMap imap
    r <- concreteUnmutatedGlobalReadWithPopulatedChunks sym mm im cache globalBlk ConcreteMutable IS.empty bv2 ptr
    pure (isNothing r)
  assertBool "non-contiguous regions should return Nothing" result

overlappingRegionsReturnsNothing :: TestTree
overlappingRegionsReturnsNothing = testImmutableRead MC.Addr32
  "Overlapping regions returns Nothing"
  [(100, [0xAA, 0xBB, 0xCC]), (102, [0xDD, 0xEE])]  -- Intervals [100,103) and [102,104) overlap
  []
  100
  bv4
  Nothing

readBeforeChunkLowerBoundReturnsNothing :: TestTree
readBeforeChunkLowerBoundReturnsNothing = testImmutableRead MC.Addr64
  "Read before chunk lower bound returns Nothing (64-bit)"
  [(2, [0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x11, 0x22])]
  []
  0  -- read starts at 0, but chunk starts at 2
  bv4
  Nothing

-- | The immutable map only contains the immutable chunk; the mutable
-- chunk at [102, 104) lives in memMutableTable and is not passed to
-- concreteImmutableGlobalRead.
readAdjacentMutableChunkReturnsJust :: TestTree
readAdjacentMutableChunkReturnsJust = testImmutableRead MC.Addr32
  "Read with adjacent mutable chunk returns Just"
  [(100, [0xAA, 0xBB])]
  []
  100
  bv2
  (Just [0xAA, 0xBB])

emptyMemoryReturnsNothing :: TestTree
emptyMemoryReturnsNothing = testImmutableRead MC.Addr32
  "Empty memory returns Nothing"
  []  -- no chunks
  []
  100
  bv1
  Nothing

addressOverflowReturnsNothing :: TestTree
addressOverflowReturnsNothing = testImmutableRead MC.Addr32
  "Address overflow returns Nothing"
  [(w32Max - 2, [0xAA, 0xBB, 0xCC, 0xDD, 0xEE])]  -- Enough bytes, but addr + 4 overflows
  []
  (w32Max - 2)
  bv4
  Nothing

addressOverflowAtZeroReturnsNothing :: TestTree
addressOverflowAtZeroReturnsNothing = testImmutableRead MC.Addr32
  "Address overflow wrapping to zero returns Nothing"
  [(0, [0x00, 0x01]), (w32Max - 2, [0xAA, 0xBB, 0xCC, 0xDD, 0xEE])]
  []
  (w32Max - 1)  -- Reading 4 bytes would wrap to address 2
  bv4
  Nothing

------------------------------------------------------------------------
-- Property-based test: Generator configuration
------------------------------------------------------------------------

-- | Distribution of gap sizes between chunks (in bytes).
gapSizeDistribution :: [(Int, Gen Word32)]
gapSizeDistribution =
  [ (5, Gen.word32 (Range.exponential 0 100))           -- small gaps (common case)
  , (3, Gen.word32 (Range.exponential 100 10000))       -- medium gaps
  , (2, Gen.word32 (Range.exponential 10000 (maxBound `div` 100)))  -- large gaps, high addresses
  ]

-- | Distribution of chunk sizes (in bytes).
chunkSizeDistribution :: [(Int, Gen Int)]
chunkSizeDistribution =
  [ (5, Gen.int (Range.exponential 1 16))           -- small chunks (common)
  , (3, Gen.int (Range.exponential 16 256))         -- medium chunks
  , (2, Gen.int (Range.exponential 256 4096))       -- large chunks
  ]

-- | Distribution of read offsets (addresses).
readOffsetDistribution :: [(Int, Gen Word32)]
readOffsetDistribution =
  [ (5, Gen.word32 (Range.exponential 0 10000))                      -- low addresses (common)
  , (3, Gen.word32 (Range.exponential 10000 1000000))                -- mid addresses
  , (2, Gen.word32 (Range.exponential 1000000 (maxBound - 100))) -- high addresses
  , (1, Gen.word32 (Range.linear (maxBound - 100) maxBound))    -- near overflow
  ]

-- | Distribution of read sizes (in bytes).
readSizeDistribution :: [(Int, Gen Int)]
readSizeDistribution =
  [ (5, Gen.element [1, 2, 4])           -- common small sizes
  , (2, pure 8)                           -- 8-byte reads
  , (1, pure 16)                          -- 16-byte reads (128-bit)
  , (1, pure 32)                          -- 32-byte reads (256-bit)
  ]

-- | Distribution of block numbers for read requests.
blockNumberDistribution :: [(Int, Gen Natural)]
blockNumberDistribution =
  [ (95, pure globalBlock)  -- Correct block (most common)
  , (3, pure 0)             -- Block 0 (wrong)
  , (2, pure 2)             -- Block 2 (wrong)
  ]

------------------------------------------------------------------------
-- Property-based test
------------------------------------------------------------------------

-- | Specification for a single memory chunk.
data MemChunkSpec = MemChunkSpec
  { mcsBaseAddr   :: !Word32         -- Base address in memory (also index in msBytes)
  , mcsLength     :: !Int            -- Length of the chunk
  , mcsMutability :: !CL.Mutability
  } deriving (Show)

-- | A memory space with bytes and non-overlapping chunk specifications.
data MemorySpace = MemorySpace
  { msBytes  :: !BS.ByteString   -- The full memory (ByteString index = address)
  , msChunks :: ![MemChunkSpec]  -- Non-overlapping chunks
  } deriving (Show)

-- | Extract a slice of bytes from a ByteString.
sliceBytes :: BS.ByteString -> Word32 -> Int -> [Word8]
sliceBytes bs offset len = BS.unpack $ BS.take len $ BS.drop (fromIntegral offset) bs

-- | Build an IntervalMap containing only immutable chunks from a MemorySpace.
-- This mirrors how concreteImmutableGlobalRead only receives memImmutableTable.
memorySpaceToImmutableIntervalMap ::
  MemorySpace ->
  IM.IntervalMap (MC.MemWord 32) (SymbolicMemChunk sym)
memorySpaceToImmutableIntervalMap memSpace =
  let chunks =
        [ ( word32ToWord64 (mcsBaseAddr s)
          , mkChunk chunkBytes )
        | s <- msChunks memSpace
        , mcsMutability s == CL.Immutable
        , let chunkBytes = sliceBytes (msBytes memSpace) (mcsBaseAddr s) (mcsLength s)
        ]
  in mkIntervalMap chunks

-- | Build a mutable interval map from a MemorySpace (only mutable chunks).
memorySpaceToMutableIntervalMap ::
  MemorySpace ->
  IM.IntervalMap (MC.MemWord 32) (SymbolicMemChunk sym)
memorySpaceToMutableIntervalMap memSpace =
  let chunks =
        [ ( word32ToWord64 (mcsBaseAddr s)
          , mkChunk chunkBytes )
        | s <- msChunks memSpace
        , mcsMutability s == CL.Mutable
        , let chunkBytes = sliceBytes (msBytes memSpace) (mcsBaseAddr s) (mcsLength s)
        ]
  in mkIntervalMap chunks

-- | Build split mutable/immutable maps from a MemorySpace,
-- matching the split-map API of mkGlobalPointerValidityPredCommon.
memorySpaceToSplitMaps ::
  MemorySpace ->
  ( MutableIntervalMap (MC.MemWord 32) ()
  , ImmutableIntervalMap (MC.MemWord 32) ()
  )
memorySpaceToSplitMaps memSpace =
  ( MutableIntervalMap $ IM.fromList
      [ (iv, ()) | s <- msChunks memSpace, mcsMutability s == CL.Mutable
                  , let iv = mkIv s ]
  , ImmutableIntervalMap $ IM.fromList
      [ (iv, ()) | s <- msChunks memSpace, mcsMutability s == CL.Immutable
                  , let iv = mkIv s ]
  )
  where
    mkIv s = IMI.IntervalCO
      (checkedToMemWord @32 (word32ToWord64 (mcsBaseAddr s)))
      (checkedToMemWord @32 (word32ToWord64 (mcsBaseAddr s) + fromIntegral (mcsLength s)))

-- | Generate a memory space with random bytes and non-overlapping chunks.
-- The ByteString is large enough that ByteString[i] corresponds to address i.
genMemorySpace :: Gen MemorySpace
genMemorySpace = do
  -- Generate the full memory (0 to 128KB, biased toward smaller sizes for speed)
  memSize <- Gen.int (Range.exponential 0 (128 * 1024))
  memBytes <- BS.pack <$> Gen.list (Range.singleton memSize) (Gen.word8 Range.linearBounded)

  -- Generate 0-50 non-overlapping chunks, biased toward fewer chunks for speed
  n <- Gen.int (Range.exponential 0 50)
  chunks <- go n 0 []
  pure (MemorySpace memBytes chunks)
  where
    go 0 _ acc = pure (reverse acc)
    go remaining cursor acc = do
      gap <- Gen.frequency gapSizeDistribution
      let base = cursor + gap
      if base < cursor
        then pure (reverse acc)  -- overflow, stop generating chunks
        else do
          len <- Gen.frequency chunkSizeDistribution
          mut <- Gen.element [CL.Mutable, CL.Immutable]
          let spec = MemChunkSpec
                { mcsBaseAddr = base
                , mcsLength = len
                , mcsMutability = mut
                }
          let nextCursor = base + fromIntegral len
          if nextCursor < base
            then pure (reverse acc)  -- overflow, stop
            else go (remaining - 1) nextCursor (spec : acc)

-- | Generate a read request.
data ReadRequest = ReadRequest
  { rrBlockNum :: !Natural
  , rrOffset   :: !Word32
  , rrSize     :: !Int  -- 1, 2, 4, 8, etc.
  } deriving (Show)

genReadRequest :: Gen ReadRequest
genReadRequest = do
  blk <- Gen.frequency blockNumberDistribution
  off <- Gen.frequency readOffsetDistribution
  sz <- Gen.frequency readSizeDistribution
  pure (ReadRequest blk off sz)

-- | Extract concrete bytes from an LLVMPtr result (little-endian).
-- For a little-endian BVMemRepr of N bytes, byte 0 is in the least significant bits.
extractLEBytes ::
  WI.IsExpr (WI.SymExpr sym) =>
  CL.LLVMPtr sym w ->
  Int ->
  Maybe [Word8]
extractLEBytes ptr numBytes = do
  bv <- WI.asBV (CLP.llvmPointerOffset ptr)
  let val = BV.asUnsigned bv
  pure [ fromIntegral ((val `shiftR` (8 * i)) .&. 0xFF)
       | i <- [0 .. numBytes - 1]
       ]

-- | Property: when concreteUnmutatedGlobalRead returns Just, the bytes match
-- the actual memory contents.
prop_concreteUnmutatedGlobalRead :: TestTree
prop_concreteUnmutatedGlobalRead = testPropertyNamed
  "concreteUnmutatedGlobalRead returns correct data"
  "prop_concreteUnmutatedGlobalRead"
  $ withTests 512 $ property $ do
    memSpace <- forAll genMemorySpace
    req <- forAll genReadRequest

    -- We do all assertion logic inside IO since the result type is sym-dependent.
    -- Return either Nothing (function declined) or Just (list of bytes).
    result <- evalIO $ withSym $ \sym -> do
      cache <- mkByteCache sym
      let mutMap = memorySpaceToMutableIntervalMap memSpace
      let immutMap = memorySpaceToImmutableIntervalMap memSpace
      globalBlk <- WI.natLit sym globalBlock
      ptr <- mkPtr sym MC.Addr32 (rrBlockNum req) (word32ToWord64 (rrOffset req))

      SomeBVMemRepr repr <-
        case bvMemReprForSize (rrSize req) of
          Nothing -> fail $ "bvMemReprForSize failed for size " ++ show (rrSize req) ++ " (generator bug)"
          Just r -> pure r

      let mm = MutableIntervalMap mutMap
          im = ImmutableIntervalMap immutMap
      r <- concreteUnmutatedGlobalReadWithPopulatedChunks sym mm im cache globalBlk ConcreteMutable IS.empty repr ptr
      pure $ case r of
        Nothing -> Nothing
        Just v -> extractLEBytes v (rrSize req)

    case result of
      Nothing -> success  -- conservative: always OK to return Nothing
      Just actualBytes -> do
        let expectedBytes = sliceBytes (msBytes memSpace) (rrOffset req) (rrSize req)
        actualBytes === expectedBytes

-- | Property: concreteUnmutatedGlobalRead and mkGlobalPointerValidityPredCommon
-- must be consistent:
--
-- * If the read succeeds, the validity predicate must say True.
-- * If the validity predicate says False, the read must not succeed.
--
-- (These are contrapositives, but testing both catches different failure modes.)
--
-- Note: the validity predicate checks a single offset, while the read checks a
-- range. So the read can fail even when validity is True (e.g., multi-byte read
-- past end of region). We only test when the block number matches.
prop_readValidityConsistency :: TestTree
prop_readValidityConsistency = testPropertyNamed
  "concreteUnmutatedGlobalRead consistent with validity predicate"
  "prop_readValidityConsistency"
  $ withTests 512 $ property $ do
    memSpace <- forAll genMemorySpace
    off <- forAll (Gen.frequency readOffsetDistribution)
    sz <- forAll (Gen.frequency readSizeDistribution)

    (readSucceeded, validityResult) <- evalIO $ withSym $ \sym -> do
      let ?processMacawAssert = defaultProcessMacawAssertion
      cache <- mkByteCache sym
      let mutMap = memorySpaceToMutableIntervalMap memSpace
      let immutMap = memorySpaceToImmutableIntervalMap memSpace
      let blk = 0 :: Natural
      globalBlk <- WI.natLit sym blk
      ptr <- mkPtr sym MC.Addr32 blk (word32ToWord64 off)

      SomeBVMemRepr repr <-
        case bvMemReprForSize sz of
          Nothing -> fail $ "bvMemReprForSize failed for size " ++ show sz ++ " (generator bug)"
          Just r -> pure r

      let mm = MutableIntervalMap mutMap
          im = ImmutableIntervalMap immutMap
      readResult <- concreteUnmutatedGlobalReadWithPopulatedChunks sym mm im cache globalBlk ConcreteMutable IS.empty repr ptr

      -- Build split maps matching the production API for validity predicate
      let (validMutMap, validImmutMap) = memorySpaceToSplitMaps memSpace
      let ptrEntry = CS.RegEntry (CL.LLVMPointerRepr WI.knownNat) ptr
      let puse = MS.PointerUse Nothing MS.PointerRead
      vResult <- mkGlobalPointerValidityPredCommon validMutMap validImmutMap sym puse Nothing ptrEntry
      let vr = case vResult of
                 Nothing -> Nothing
                 Just (CB.LabeledPred p _) -> Just (WI.asConstantPred p)
      pure (isJust readResult, vr)

    case (readSucceeded, validityResult) of
      -- Read succeeded → validity must be True
      (True, Just (Just True)) -> success
      (True, _) -> do
        footnote "Read succeeded but validity predicate was not True"
        failure
      -- Validity False → read must not succeed
      (False, Just (Just False)) -> success
      -- Read failed, validity True → OK
      (False, Just (Just True)) -> success
      -- Anything else unexpected for concrete block-0 pointer
      (_, _) -> do
        footnote $ "Unexpected: readSucceeded=" ++ show readSucceeded
                 ++ " validity=" ++ show validityResult
        failure

------------------------------------------------------------------------
-- Test tree
------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Lazy memory model"
  [ testGroup "Unit tests"
      [ testGroup "Basic reads"
          [ read1
          , read2
          , read4
          , read8
          , readFromOffset
          , readFromOffsetSymbolicBytes
          , readFullSymbolicBytes
          , readSpanningSymbolicBytes
          , readSpanningConcreteIntoSymbolic
          , readSpanningContiguousChunks
          ]
      , testGroup "Edge cases"
          [ readFromAddressZero
          , readAtChunkBoundary
          , readLastByteOfChunk
          , readNearMaxBound
          ]
      , testGroup "Failure cases"
          [ wrongBlockReturnsNothing
          , symbolicOffsetReturnsNothing
          , unpopulatedMutableRegionReturnsJust
          , populatedMutableRegionReturnsNothing
          , symbolicMutableUnpopulatedReturnsNothing
          , notEnoughBytesReturnsNothing
          , nonContiguousRegionsReturnsNothing
          , overlappingRegionsReturnsNothing
          , readBeforeChunkLowerBoundReturnsNothing
          , readAdjacentMutableChunkReturnsJust
          , emptyMemoryReturnsNothing
          , addressOverflowReturnsNothing
          , addressOverflowAtZeroReturnsNothing
          ]
      ]
  , testGroup "Property-based tests"
      [ prop_concreteUnmutatedGlobalRead
      , prop_readValidityConsistency
      ]
  ]
