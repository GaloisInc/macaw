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
import qualified Data.Macaw.Symbolic.Memory.ByteCache as MBC
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
import           Test.Tasty.HUnit (assertBool, testCase)

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

-- | Build a SymbolicMemChunk from concrete bytes using a ByteCache.
mkChunk ::
  MBC.ByteCache sym ->
  [Word8] ->
  CL.Mutability ->
  SymbolicMemChunk sym
mkChunk cache bytes mut = SymbolicMemChunk
  { smcBytes = Seq.fromList (map (MBC.indexByteCache cache) bytes)
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

-- | Build an IntervalMap from a MemorySpace.
-- Extracts bytes from the ByteString and creates symbolic chunks.
memorySpaceToIntervalMap ::
  MBC.ByteCache sym ->
  MemorySpace ->
  IM.IntervalMap (MC.MemWord W) (SymbolicMemChunk sym)
memorySpaceToIntervalMap cache memSpace =
  let chunks = [ (mcsBaseAddr s, mkChunk cache chunkBytes (mcsMutability s))
               | s <- msChunks memSpace
               , let chunkBytes = BS.unpack $ BS.take (mcsLength s) $ BS.drop (fromIntegral (mcsBaseAddr s)) (msBytes memSpace)
               ]
  in mkIntervalMap chunks

-- | Extract concrete bytes from an LLVMPtr result (little-endian).
-- For a little-endian BVMemRepr of N bytes, the BV stores byte 0 in the
-- least significant 8 bits.
extractLEBytes ::
  WI.IsExpr (WI.SymExpr sym) =>
  CL.LLVMPtr sym w ->
  Int ->
  Maybe [Word8]
extractLEBytes ptr numBytes =
  case WI.asBV (CLP.llvmPointerOffset ptr) of
    Just bv ->
      let val = BV.asUnsigned bv
      in Just [ fromIntegral ((val `shiftR` (8 * i)) .&. 0xFF)
              | i <- [0 .. numBytes - 1]
              ]
    Nothing -> Nothing

-- | Existential wrapper for a BVMemRepr with some width.
data SomeMemRepr where
  SomeMemRepr :: (1 WI.<= w) => MC.MemRepr (BVType w) -> SomeMemRepr

-- | Get the appropriate MemRepr for a given size in bytes.
memReprForSize :: Int -> Maybe SomeMemRepr
memReprForSize = \case
  1  -> Just (SomeMemRepr bv1)
  2  -> Just (SomeMemRepr bv2)
  4  -> Just (SomeMemRepr bv4)
  8  -> Just (SomeMemRepr bv8)
  16 -> Just (SomeMemRepr bv16)
  32 -> Just (SomeMemRepr bv32)
  _  -> Nothing

------------------------------------------------------------------------
-- Unit tests
------------------------------------------------------------------------

-- | Pointer block /= global block => Nothing
wrongBlockReturnsNothing :: TestTree
wrongBlockReturnsNothing = testCase "Wrong block returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- MBC.mkByteCache sym
    let chunk = mkChunk cache [0xAA, 0xBB] CL.Immutable
    let imap = mkIntervalMap [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkPtr sym 2 100  -- block 2, but global is block 1
    r <- concreteImmutableGlobalRead sym imap globalBlk bv1 ptr
    pure (isNothing r)
  assertBool "wrong block should return Nothing" result

-- | Symbolic (non-concrete) pointer offset => Nothing
symbolicOffsetReturnsNothing :: TestTree
symbolicOffsetReturnsNothing = testCase "Symbolic offset returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- MBC.mkByteCache sym
    let chunk = mkChunk cache [0xAA, 0xBB] CL.Immutable
    let imap = mkIntervalMap [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    blkSym <- WI.natLit sym globalBlock
    offSym <- WI.freshConstant sym (WI.safeSymbol "off") (WI.BaseBVRepr (WI.knownNat @W))
    let ptr = CLP.LLVMPointer blkSym offSym
    r <- concreteImmutableGlobalRead sym imap globalBlk bv1 ptr
    pure (isNothing r)
  assertBool "symbolic offset should return Nothing" result

-- | Memory marked Mutable => Nothing
mutableRegionReturnsNothing :: TestTree
mutableRegionReturnsNothing = testCase "Mutable region returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- MBC.mkByteCache sym
    let chunk = mkChunk cache [0xAA, 0xBB] CL.Mutable
    let imap = mkIntervalMap [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym 100
    r <- concreteImmutableGlobalRead sym imap globalBlk bv1 ptr
    pure (isNothing r)
  assertBool "mutable region should return Nothing" result

-- | Read extends past chunk end => Nothing
notEnoughBytesReturnsNothing :: TestTree
notEnoughBytesReturnsNothing = testCase "Not enough bytes returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- MBC.mkByteCache sym
    let chunk = mkChunk cache [0xAA, 0xBB] CL.Immutable
    let imap = mkIntervalMap [(100, chunk)]
    globalBlk <- WI.natLit sym globalBlock
    ptr <- mkGlobalPtr sym 100
    r <- concreteImmutableGlobalRead sym imap globalBlk bv4 ptr
    pure (isNothing r)
  assertBool "not enough bytes should return Nothing" result

-- | Gap between chunks => Nothing
nonContiguousRegionsReturnsNothing :: TestTree
nonContiguousRegionsReturnsNothing = testCase "Non-contiguous regions returns Nothing" $ do
  result <- withSym $ \sym -> do
    cache <- MBC.mkByteCache sym
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

------------------------------------------------------------------------
-- Property-based test: Generator configuration
------------------------------------------------------------------------

-- | Distribution of gap sizes between chunks (in bytes).
gapSizeDistribution :: [(Int, Gen Word32)]
gapSizeDistribution =
  [ (5, Gen.word32 (Range.linear 0 100))           -- small gaps (common case)
  , (3, Gen.word32 (Range.linear 100 10000))       -- medium gaps
  , (2, Gen.word32 (Range.exponential 10000 (maxBound `div` 100)))  -- large gaps, high addresses
  ]

-- | Distribution of chunk sizes (in bytes).
chunkSizeDistribution :: [(Int, Gen Int)]
chunkSizeDistribution =
  [ (5, Gen.int (Range.linear 1 16))           -- small chunks (common)
  , (3, Gen.int (Range.linear 16 256))         -- medium chunks
  , (2, Gen.int (Range.linear 256 4096))       -- large chunks
  ]

-- | Distribution of read offsets (addresses).
readOffsetDistribution :: [(Int, Gen Word32)]
readOffsetDistribution =
  [ (5, Gen.word32 (Range.linear 0 10000))                      -- low addresses (common)
  , (3, Gen.word32 (Range.linear 10000 1000000))                -- mid addresses
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

------------------------------------------------------------------------
-- Property-based test: Data types
------------------------------------------------------------------------

-- | A memory space with bytes and non-overlapping chunk specifications.
data MemorySpace = MemorySpace
  { msBytes  :: !BS.ByteString   -- The full memory (ByteString index = address)
  , msChunks :: ![MemChunkSpec]  -- Non-overlapping chunks
  } deriving (Show)

-- | Specification for a single memory chunk.
data MemChunkSpec = MemChunkSpec
  { mcsBaseAddr   :: !Word32         -- Base address in memory (also index in msBytes)
  , mcsLength     :: !Int            -- Length of the chunk
  , mcsMutability :: !CL.Mutability
  } deriving (Show)

-- | Generate a memory space with random bytes and non-overlapping chunks.
-- The ByteString is large enough that ByteString[i] corresponds to address i.
genMemorySpace :: Gen MemorySpace
genMemorySpace = do
  -- Generate the full memory (0 to 128KB to test various sizes including small/empty)
  memSize <- Gen.int (Range.linear 0 (128 * 1024))
  memBytes <- BS.pack <$> Gen.list (Range.singleton memSize) (Gen.word8 Range.linearBounded)

  -- Generate 0-50 non-overlapping chunks to test sparse/dense patterns
  n <- Gen.int (Range.linear 0 50)
  chunks <- go n 0 []
  pure (MemorySpace memBytes chunks)
  where
    go 0 _ acc = pure (reverse acc)
    go remaining cursor acc = do
      -- Large gaps to test sparse memory and high addresses
      gap <- Gen.frequency gapSizeDistribution
      let base = cursor + gap

      -- Check for overflow when computing base address
      if base < cursor
        then pure (reverse acc)  -- overflow, stop generating chunks
        else do
          -- Variable chunk sizes from tiny to large
          len <- Gen.frequency chunkSizeDistribution

          mut <- Gen.element [CL.Mutable, CL.Immutable]
          let spec = MemChunkSpec
                { mcsBaseAddr = base
                , mcsLength = len
                , mcsMutability = mut
                }

          -- Check for overflow when computing next cursor
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
  blk <- Gen.element [0, globalBlock, 2]  -- different blocks to test block mismatches
  off <- Gen.frequency readOffsetDistribution
  sz <- Gen.frequency readSizeDistribution
  pure (ReadRequest blk off sz)

-- | Property: when concreteImmutableGlobalRead returns Just, the bytes match
-- the actual memory contents.
prop_concreteImmutableGlobalRead :: TestTree
prop_concreteImmutableGlobalRead = testPropertyNamed
  "concreteImmutableGlobalRead returns correct data"
  "prop_concreteImmutableGlobalRead"
  $ withTests 256 $ property $ do
    memSpace <- forAll genMemorySpace
    req <- forAll genReadRequest

    -- We do all assertion logic inside IO since the result type is sym-dependent.
    -- Return either Nothing (function declined) or Just (list of bytes).
    result <- evalIO $ withSym $ \sym -> do
      cache <- MBC.mkByteCache sym
      let imap = memorySpaceToIntervalMap cache memSpace
      globalBlk <- WI.natLit sym globalBlock
      ptr <- mkPtr sym (rrBlockNum req) (rrOffset req)

      case memReprForSize (rrSize req) of
        Nothing -> pure Nothing
        Just (SomeMemRepr repr) -> do
          r <- concreteImmutableGlobalRead sym imap globalBlk repr ptr
          pure $ case r of
            Nothing -> Nothing
            Just v -> extractLEBytes v (rrSize req)

    case result of
      Nothing -> success  -- conservative: always OK to return Nothing
      Just actualBytes -> do
        let expectedBytes = BS.unpack $ BS.take (rrSize req) $ BS.drop (fromIntegral (rrOffset req)) (msBytes memSpace)
        actualBytes === expectedBytes

------------------------------------------------------------------------
-- Test tree
------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Lazy memory model"
  [ wrongBlockReturnsNothing
  , symbolicOffsetReturnsNothing
  , mutableRegionReturnsNothing
  , notEnoughBytesReturnsNothing
  , nonContiguousRegionsReturnsNothing
  , prop_concreteImmutableGlobalRead
  ]
