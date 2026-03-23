{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
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
import qualified Data.IntervalMap.Strict as IM
import qualified Data.IntervalMap.Interval as IMI
import           Data.Maybe (isNothing)
import qualified Data.Sequence as Seq
import           Data.Word (Word8, Word32)
import           Numeric.Natural (Natural)

import qualified Data.Macaw.CFG as MC
import           Data.Macaw.Types (BVType)
import           Data.Macaw.Symbolic.Memory.Lazy.Internal
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.LLVM.MemModel.Pointer as CLP
import qualified What4.Expr as WE
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import           Data.Parameterized.Nonce (newIONonceGenerator)
import           Data.Parameterized.Some (Some(..))

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.Hedgehog (testPropertyNamed)
import           Test.Tasty.HUnit ((@?=), assertBool, testCase)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- | Width used in tests (must have a MemWidth instance: 32 or 64)
type W = 32

-- | Global memory block number used in tests.
globalBlock :: Natural
globalBlock = 1

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
  Natural ->
  Word32 ->
  IO (CL.LLVMPtr sym W)
mkPtr sym blk off = do
  blkSym <- WI.natLit sym blk
  offSym <- WI.bvLit sym (WI.knownNat @W) (BV.word32 off)
  pure (CLP.LLVMPointer blkSym offSym)

-- | Build an LLVMPointer in the global block with the given offset.
mkGlobalPtr ::
  WI.IsExprBuilder sym =>
  sym ->
  Word32 ->
  IO (CL.LLVMPtr sym W)
mkGlobalPtr sym off = mkPtr sym globalBlock off

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

-- | Build a SymbolicMemChunk from concrete bytes using a ByteCache.
mkChunk ::
  ByteCache sym ->
  [Word8] ->
  CL.Mutability ->
  SymbolicMemChunk sym
mkChunk cache bytes mut = SymbolicMemChunk
  { smcBytes = Seq.fromList (map (indexByteCache cache) bytes)
  , smcMutability = mut
  }

-- | Build an IntervalMap from a list of (base, chunk) pairs.
-- Uses IntervalCO (closed-open) intervals.
mkIntervalMap ::
  [(Word32, SymbolicMemChunk sym)] ->
  IM.IntervalMap (MC.MemWord W) (SymbolicMemChunk sym)
mkIntervalMap entries = IM.fromList
  [ (IMI.IntervalCO (fromIntegral lo) (fromIntegral lo + fromIntegral (Seq.length (smcBytes c))), c)
  | (lo, c) <- entries
  ]

-- | Helper to test an immutable read operation and verify the result.
-- Creates an interval map from the provided chunks, performs the read, and checks the result.
testImmutableRead ::
  String ->                 -- ^ Test name
  [(Word32, [Word8])] ->    -- ^ Memory chunks (base address, bytes)
  Word32 ->                 -- ^ Read address
  MC.MemRepr (BVType w) ->  -- ^ Read size/type
  Maybe [Word8] ->          -- ^ Expected result (Nothing = should fail)
  TestTree
testImmutableRead name chunks readAddr repr expected = testCase name $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let memChunks = [(base, mkChunk cache bytes CL.Immutable) | (base, bytes) <- chunks]
    let imap = mkIntervalMap memChunks
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym readAddr
    r <- concreteImmutableGlobalRead sym imap globalBlk repr ptr
    pure $ case r of
      Nothing -> Nothing
      Just val -> extractLEBytes val (fromIntegral $ MC.memReprBytes repr)
  result @?= expected

------------------------------------------------------------------------
-- Unit tests
------------------------------------------------------------------------

read1 :: TestTree
read1 = testImmutableRead
  "One-byte read"
  [(100, [0xAA, 0xBB])]
  100
  bv1
  (Just [0xAA])

read2 :: TestTree
read2 = testImmutableRead
  "Two-byte read"
  [(100, [0xAA, 0xBB, 0xCC])]
  100
  bv2
  (Just [0xAA, 0xBB])

read4 :: TestTree
read4 = testImmutableRead
  "Four-byte read"
  [(200, [0x11, 0x22, 0x33, 0x44, 0x55])]
  200
  bv4
  (Just [0x11, 0x22, 0x33, 0x44])

readFromOffset :: TestTree
readFromOffset = testImmutableRead
  "Read from offset within chunk"
  [(300, [0x10, 0x20, 0x30, 0x40, 0x50])]
  302  -- offset 2 into the chunk
  bv2
  (Just [0x30, 0x40])

readSpanningContiguousChunks :: TestTree
readSpanningContiguousChunks = testImmutableRead
  "Read spanning contiguous chunks"
  [(100, [0xAA, 0xBB]), (102, [0xCC, 0xDD])]  -- Two contiguous chunks
  101  -- start in first chunk, span into second
  bv2
  (Just [0xBB, 0xCC])

read8 :: TestTree
read8 = testImmutableRead
  "Eight-byte read"
  [(1000, [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09])]
  1000
  bv8
  (Just [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08])

readFromAddressZero :: TestTree
readFromAddressZero = testImmutableRead
  "Read from address zero"
  [(0, [0xFF, 0xFE, 0xFD, 0xFC])]
  0
  bv4
  (Just [0xFF, 0xFE, 0xFD, 0xFC])

readAtChunkBoundary :: TestTree
readAtChunkBoundary = testImmutableRead
  "Read ending exactly at chunk boundary"
  [(100, [0xAA, 0xBB, 0xCC, 0xDD])]
  100
  bv4
  (Just [0xAA, 0xBB, 0xCC, 0xDD])

readLastByteOfChunk :: TestTree
readLastByteOfChunk = testImmutableRead
  "Read last byte of chunk"
  [(100, [0xAA, 0xBB, 0xCC])]
  102
  bv1
  (Just [0xCC])

readNearMaxBound :: TestTree
readNearMaxBound = testImmutableRead
  "Read from near maxBound"
  [(maxBound - 10, [0x01, 0x02, 0x03, 0x04, 0x05])]
  (maxBound - 10)
  bv4
  (Just [0x01, 0x02, 0x03, 0x04])

wrongBlockReturnsNothing :: TestTree
wrongBlockReturnsNothing = testCase "Wrong block returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let chunk = mkChunk cache [0xAA, 0xBB] CL.Immutable
    let imap = mkIntervalMap [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkPtr sym 2 100  -- block 2, but global is block 1
    r <- concreteImmutableGlobalRead sym imap globalBlk bv1 ptr
    pure (isNothing r)
  assertBool "wrong block should return Nothing" result

symbolicOffsetReturnsNothing :: TestTree
symbolicOffsetReturnsNothing = testCase "Symbolic offset returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let chunk = mkChunk cache [0xAA, 0xBB] CL.Immutable
    let imap = mkIntervalMap [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    blkSym <- WI.natLit sym globalBlock
    offSym <- WI.freshConstant sym (WI.safeSymbol "off") (WI.BaseBVRepr (WI.knownNat @W))
    let ptr = CLP.LLVMPointer blkSym offSym
    r <- concreteImmutableGlobalRead sym imap globalBlk bv1 ptr
    pure (isNothing r)
  assertBool "symbolic offset should return Nothing" result

mutableRegionReturnsNothing :: TestTree
mutableRegionReturnsNothing = testCase "Mutable region returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let chunk = mkChunk cache [0xAA, 0xBB] CL.Mutable
    let imap = mkIntervalMap [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym 100
    r <- concreteImmutableGlobalRead sym imap globalBlk bv1 ptr
    pure (isNothing r)
  assertBool "mutable region should return Nothing" result

notEnoughBytesReturnsNothing :: TestTree
notEnoughBytesReturnsNothing = testImmutableRead
  "Not enough bytes returns Nothing"
  [(100, [0xAA, 0xBB])]
  100
  bv4
  Nothing

nonContiguousRegionsReturnsNothing :: TestTree
nonContiguousRegionsReturnsNothing = testCase "Non-contiguous regions returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let chunk1 = mkChunk cache [0xAA] CL.Immutable
    let chunk2 = mkChunk cache [0xBB] CL.Immutable
    let imap = IM.fromList
          [ (IMI.IntervalCO 100 101, chunk1)
          , (IMI.IntervalCO 102 103, chunk2)
          ]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym 100
    r <- concreteImmutableGlobalRead sym imap globalBlk bv2 ptr
    pure (isNothing r)
  assertBool "non-contiguous regions should return Nothing" result

overlappingRegionsReturnsNothing :: TestTree
overlappingRegionsReturnsNothing = testImmutableRead
  "Overlapping regions returns Nothing"
  [(100, [0xAA, 0xBB, 0xCC]), (102, [0xDD, 0xEE])]  -- Intervals [100,103) and [102,104) overlap
  100
  bv4
  Nothing

readAdjacentMutableChunkReturnsJust :: TestTree
readAdjacentMutableChunkReturnsJust = testCase "Read with adjacent mutable chunk returns Just" $ do
  result <- withSym $ \sym -> do
    cache <- mkByteCache sym
    let immChunk = mkChunk cache [0xAA, 0xBB] CL.Immutable
    let mutChunk = mkChunk cache [0xCC, 0xDD] CL.Mutable
    -- [100, 102) immutable, [102, 104) mutable
    let imap = IM.fromList
          [ (IMI.IntervalCO 100 102, immChunk)
          , (IMI.IntervalCO 102 104, mutChunk)
          ]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym 100
    r <- concreteImmutableGlobalRead sym imap globalBlk bv2 ptr
    pure $ case r of
      Nothing -> Nothing
      Just val -> extractLEBytes val 2
  result @?= Just [0xAA, 0xBB]

emptyMemoryReturnsNothing :: TestTree
emptyMemoryReturnsNothing = testImmutableRead
  "Empty memory returns Nothing"
  []  -- no chunks
  100
  bv1
  Nothing

addressOverflowReturnsNothing :: TestTree
addressOverflowReturnsNothing = testImmutableRead
  "Address overflow returns Nothing"
  [(maxBound - 2, [0xAA, 0xBB, 0xCC, 0xDD, 0xEE])]  -- Enough bytes, but addr + 4 overflows
  (maxBound - 2)
  bv4
  Nothing

addressOverflowAtZeroReturnsNothing :: TestTree
addressOverflowAtZeroReturnsNothing = testImmutableRead
  "Address overflow wrapping to zero returns Nothing"
  [(0, [0x00, 0x01]), (maxBound - 2, [0xAA, 0xBB, 0xCC, 0xDD, 0xEE])]
  (maxBound - 1)  -- Reading 4 bytes would wrap to address 2
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

-- | Build an IntervalMap from a MemorySpace.
-- Extracts bytes from the ByteString and creates symbolic chunks.
memorySpaceToIntervalMap ::
  ByteCache sym ->
  MemorySpace ->
  IM.IntervalMap (MC.MemWord W) (SymbolicMemChunk sym)
memorySpaceToIntervalMap cache memSpace =
  let chunks =
        [ (mcsBaseAddr s, mkChunk cache chunkBytes (mcsMutability s))
        | s <- msChunks memSpace
        , let chunkBytes = sliceBytes (msBytes memSpace) (mcsBaseAddr s) (mcsLength s)
        ]
  in mkIntervalMap chunks

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

-- | Property: when concreteImmutableGlobalRead returns Just, the bytes match
-- the actual memory contents.
prop_concreteImmutableGlobalRead :: TestTree
prop_concreteImmutableGlobalRead = testPropertyNamed
  "concreteImmutableGlobalRead returns correct data"
  "prop_concreteImmutableGlobalRead"
  $ withTests 512 $ property $ do
    memSpace <- forAll genMemorySpace
    req <- forAll genReadRequest

    -- We do all assertion logic inside IO since the result type is sym-dependent.
    -- Return either Nothing (function declined) or Just (list of bytes).
    result <- evalIO $ withSym $ \sym -> do
      cache <- mkByteCache sym
      let imap = memorySpaceToIntervalMap cache memSpace
      globalBlk <- WI.natLit sym globalBlock
      ptr <- mkPtr sym (rrBlockNum req) (rrOffset req)

      SomeBVMemRepr repr <-
        case bvMemReprForSize (rrSize req) of
          Nothing -> fail $ "bvMemReprForSize failed for size " ++ show (rrSize req) ++ " (generator bug)"
          Just r -> pure r

      r <- concreteImmutableGlobalRead sym imap globalBlk repr ptr
      pure $ case r of
        Nothing -> Nothing
        Just v -> extractLEBytes v (rrSize req)

    case result of
      Nothing -> success  -- conservative: always OK to return Nothing
      Just actualBytes -> do
        let expectedBytes = sliceBytes (msBytes memSpace) (rrOffset req) (rrSize req)
        actualBytes === expectedBytes

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
          , mutableRegionReturnsNothing
          , notEnoughBytesReturnsNothing
          , nonContiguousRegionsReturnsNothing
          , overlappingRegionsReturnsNothing
          , readAdjacentMutableChunkReturnsJust
          , emptyMemoryReturnsNothing
          , addressOverflowReturnsNothing
          , addressOverflowAtZeroReturnsNothing
          ]
      ]
  , testGroup "Property-based tests"
      [ prop_concreteImmutableGlobalRead
      ]
  ]
