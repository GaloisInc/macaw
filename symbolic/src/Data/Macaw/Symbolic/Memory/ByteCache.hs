{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A cache of all 256 possible byte literals (0x00 to 0xFF).
--
-- This module provides a strict, pre-computed cache of literal byte values as
-- What4 terms to avoid allocating separate terms for each byte during memory
-- operations. For large binaries, this optimization saves gigabytes of heap.
module Data.Macaw.Symbolic.Memory.ByteCache
  ( ByteCache
  , mkByteCache
  , indexByteCache
  , indexByteCacheM
  ) where

import qualified Data.BitVector.Sized as BV
import qualified Data.Vector.Strict as Vec
import           Data.Word (Word8)
import qualified What4.Interface as WI

-- | A cache of all 256 possible byte literals @0x00@ to @0xFF@.
--
-- Constructor not exported to uphold safety invariant of 'indexByteCache'.
newtype ByteCache sym = ByteCache (Vec.Vector (WI.SymBV sym 8))

-- | Create a 'ByteCache'
--
-- Ideally, this should be called once during memory model initialization and
-- the resulting cache should be shared across all operations.
mkByteCache ::
  WI.IsExprBuilder sym =>
  sym ->
  IO (ByteCache sym)
mkByteCache sym = do
  let w8 = WI.knownNat @8
  cache <- Vec.generateM 256 $ \i ->
    WI.bvLit sym w8 (BV.word8 (fromIntegral i))
  pure (ByteCache cache)

-- | Index into the 'ByteCache' to retrieve a symbolic bitvector.
--
-- This uses unsafe indexing internally since we know:
--
-- 1. The underlying 'Vec.Vector' has exactly 256 elements (0x00 to 0xFF)
-- 2. 'Word8' values are always in the range @[0, 255]@
--
-- Therefore, the index is always in bounds and the bounds check is redundant.
indexByteCache :: ByteCache sym -> Word8 -> WI.SymBV sym 8
indexByteCache (ByteCache vec) byte = Vec.unsafeIndex vec (fromIntegral byte)
{-# INLINE indexByteCache #-}

-- | Monadic version of 'indexByteCache' that is strict in the vector.
indexByteCacheM :: Monad m => ByteCache sym -> Word8 -> m (WI.SymBV sym 8)
indexByteCacheM (ByteCache vec) byte = Vec.unsafeIndexM vec (fromIntegral byte)
{-# INLINE indexByteCacheM #-}
