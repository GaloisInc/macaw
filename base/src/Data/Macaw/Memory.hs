{-|
Copyright   : (c) Galois Inc, 2015-2018
Maintainer  : jhendrix@galois.com

Declares 'Memory', a type for representing segmented memory with permissions.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.Memory
  ( Memory
    -- * Inspecting memory
  , memAddrWidth
  , memWidth
  , memSegments
  , memAsAddrPairs
    -- * Constructing memory
  , emptyMemory
  , insertMemSegment
  , InsertError(..)
  , showInsertError
    -- * Load values
  , memBaseAddr
  , memSetBaseAddr
  , memBindSectionIndex
  , memSectionIndexMap
  , memSegmentIndexMap
  , memBindSegmentIndex
    -- * Memory segments
  , MemSegment
  , memSegment
  , segmentBase
  , RegionIndex
  , segmentOffset
  , segmentFlags
  , segmentSize
  , ppMemSegment
    -- ** MemChunk
  , MemChunk(..)
  , Relocation(..)
  , module Data.BinarySymbols
    -- ** MemChunk operations
  , forcedTakeMemChunks
  , splitMemChunks
  , SplitError(..)
    -- * MemWidth
  , MemWidth(..)
  , memWidthNatRepr
    -- * MemWord
  , MemWord
  , zeroMemWord
  , memWord
  , memWordValue
  , memWordToUnsigned
  , memWordToSigned
  , addrRead
    -- * MemInt
  , MemInt
  , memIntValue
    -- * Addresses
  , MemAddr(..)
  , absoluteAddr
  , segmentOffAddr
  , asAbsoluteAddr
  , diffAddr
  , incAddr
  , addrLeastBit
  , clearAddrLeastBit
  , asSegmentOff
    -- * Segment offsets
  , MemSegmentOff
    -- ** Queries
  , segoffSegment
  , segoffOffset
  , segoffAddr
  , segoffAsAbsoluteAddr
  , segoffBytesLeft
  , segoffContentsAfter
    -- ** Construction segment offsets.
  , resolveRegionOff
  , resolveAbsoluteAddr
  , resolveSegmentOff
    -- ** Modifying
  , incSegmentOff
  , diffSegmentOff
  , clearSegmentOffLeastBit
    -- * Reading
  , MemoryError(..)
  , addrContentsAfter
  , readByteString
  , readAddr
  , readSegmentOff
  , readWord8
  , readWord16be
  , readWord16le
  , readWord32be
  , readWord32le
  , readWord64be
  , readWord64le
  , NullTermString(..)
  , readNullTermString
    -- * AddrWidthRepr
  , AddrWidthRepr(..)
  , addrWidthReprByteCount
  , addrWidthNatRepr
  , addrWidthClass
    -- * Endianness
  , Endianness(..)
  , bytesToInteger
  , bsWord8
  , ElfBS.bsWord16be
  , ElfBS.bsWord16le
  , bsWord32
  , ElfBS.bsWord32be
  , ElfBS.bsWord32le
  , bsWord64
  , ElfBS.bsWord64be
  , ElfBS.bsWord64le
    -- * Memory search
  , findByteStringMatches
  , relativeSegmentContents
    -- * Generating [MemChunk] values from relocations.
  , RelocEntry(..)
  , ResolveFn
    -- * Deprecated declarations
  , SegmentRange
  , takeSegmentPrefix
  , splitSegmentRangeList
  , dropSegmentRangeListBytes
  , dropErrorAsMemError
  , executableSegments
  , readonlySegments
  , memWordInteger
  , memWordSigned
  , resolveAddr
  , relativeSegmentAddr
  , msegAddr
  , contentsAfterSegmentOff
  , msegSegment
  , msegOffset
  , msegByteCountAfter
  , relativeAddr
  ) where

import           Control.Monad
import           Data.BinarySymbols
import           Data.Bits
import qualified Data.ByteString as BS
import qualified Data.ElfEdit.ByteString as ElfBS
import           Data.Int (Int32, Int64)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Monoid
import           Data.Proxy
import           Data.Word
import           GHC.Natural
import           GHC.TypeLits
import           Language.Haskell.TH.Syntax
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr

import qualified Data.Macaw.Memory.Permissions as Perm

import           Prelude

------------------------------------------------------------------------
-- AddrWidthRepr

-- | An address width
data AddrWidthRepr w
   = (w ~ 32) => Addr32
     -- ^ A 32-bit address
   | (w ~ 64) => Addr64
     -- ^ A 64-bit address

deriving instance Show (AddrWidthRepr w)

instance TestEquality AddrWidthRepr where
  testEquality Addr32 Addr32 = Just Refl
  testEquality Addr64 Addr64 = Just Refl
  testEquality _ _ = Nothing

instance OrdF AddrWidthRepr where
  compareF Addr32 Addr32 = EQF
  compareF Addr32 Addr64 = LTF
  compareF Addr64 Addr32 = GTF
  compareF Addr64 Addr64 = EQF

-- | Number of bytes in addr width repr.
addrWidthReprByteCount :: AddrWidthRepr w -> Natural
addrWidthReprByteCount Addr32 = 4
addrWidthReprByteCount Addr64 = 8

-- | The nat representation of this address.
addrWidthNatRepr :: AddrWidthRepr w -> NatRepr w
addrWidthNatRepr Addr32 = knownNat
addrWidthNatRepr Addr64 = knownNat

------------------------------------------------------------------------
-- Endianness

-- | Indicates whether bytes are stored in big or little endian representation.
--
-- In a big endian representation, the most significant byte is stored first;
-- In a little endian representation, the most significant byte is stored last.
data Endianness = BigEndian | LittleEndian
  deriving (Eq, Ord, Show, Lift)

instance Hashable Endianness where
  hashWithSalt s BigEndian    = s `hashWithSalt` (0::Int)
  hashWithSalt s LittleEndian = s `hashWithSalt` (1::Int)

-- | Convert a byte string to an integer using the provided
-- endianness.
bytesToInteger :: Endianness -> BS.ByteString -> Integer
bytesToInteger BigEndian = BS.foldl' f 0
  where f x w = (x `shiftL` 8) .|. toInteger w
bytesToInteger LittleEndian = BS.foldr' f 0
  where f w x = (x `shiftL` 8) .|. toInteger w

------------------------------------------------------------------------
-- Utilities

-- | Split a bytestring into an equivalent list of byte strings with a given size.
--
-- This drops the last bits if the total length is not a multiple of the size.
regularChunks :: Int -> BS.ByteString -> [BS.ByteString]
regularChunks sz bs
  | BS.length bs < sz = []
  | otherwise = BS.take sz bs : regularChunks sz (BS.drop sz bs)

bsWord8 :: BS.ByteString -> Word8
bsWord8 bs
    | BS.length bs /= 1 = error "bsWord8 given bytestring with bad length."
    | otherwise = BS.index bs 0

-- | Convert a bytestring to an unsigned with the given endianness.
bsWord32 :: Endianness -> BS.ByteString -> Word32
bsWord32 BigEndian    = ElfBS.bsWord32be
bsWord32 LittleEndian = ElfBS.bsWord32le

bsWord64 :: Endianness -> BS.ByteString -> Word64
bsWord64 BigEndian    = ElfBS.bsWord64be
bsWord64 LittleEndian = ElfBS.bsWord64le

------------------------------------------------------------------------
-- MemWord

-- | This represents a bitvector value with `w` bits.
--
-- Operations on it require the `MemWidth` constraint to be satisfied, so in practice
-- this only works for 32 and 64-bit values.
newtype MemWord (w :: Nat) = MemWord { memWordValue :: Word64 }

-- | Equal to 0
zeroMemWord :: MemWord w
zeroMemWord = MemWord 0

-- | Convert word64 @x@ into mem word @x mod 2^w-1@.
memWord :: forall w . MemWidth w => Word64 -> MemWord w
memWord x = MemWord (x .&. addrWidthMask p)
  where p :: Proxy w
        p = Proxy

instance Hashable (MemWord w) where
  hashWithSalt s (MemWord w) = s `hashWithSalt` w

instance Show (MemWord w) where
  showsPrec _ (MemWord w) = showString "0x" . showHex w

instance Pretty (MemWord w) where
  pretty = text . show

instance Eq (MemWord w) where
  MemWord x == MemWord y = x == y

instance Ord (MemWord w) where
  compare (MemWord x) (MemWord y) = compare x y

-- | Typeclass for widths supported by memory addresses.
--
-- This only will work for 32 and 64bit values due to requirement
-- to implement `addrWidthRepr`.
class (1 <= w) => MemWidth w where

  -- | Returns @AddrWidthRepr@ to identify width of pointer.
  --
  -- The argument is ignored.
  addrWidthRepr :: p w -> AddrWidthRepr w

  -- | Returns number of bytes in addr.
  --
  -- The argument is not evaluated.
  addrSize :: p w -> Int

  -- | @addrWidthMask w@ returns @2^(8 * addrSize w) - 1@.
  addrWidthMask :: p w -> Word64

  -- | Rotates the value by the given index.
  addrRotate :: MemWord w -> Int -> MemWord w

memWidthNatRepr :: MemWidth w => NatRepr w
memWidthNatRepr = addrWidthNatRepr (addrWidthRepr memWidthNatRepr)

-- | Read an address with the given endianess.
--
-- This returns nothing if the bytestring is too short.
addrRead :: forall w . MemWidth w => Endianness -> BS.ByteString -> Maybe (MemWord w)
addrRead e s =
  case addrWidthRepr (Proxy :: Proxy w) of
    Addr32 | BS.length s < 4 -> Nothing
           | otherwise -> Just $ MemWord $ fromIntegral $ bsWord32 e s
    Addr64 | BS.length s < 8 -> Nothing
           | otherwise -> Just $ MemWord $ bsWord64 e s


-- | Return the value represented by the MemWord as an unsigned integer.
memWordToUnsigned  :: MemWord w -> Integer
memWordToUnsigned = fromIntegral . memWordValue

-- | Treat the word as a signed integer.
memWordToSigned :: MemWidth w => MemWord w -> Integer
memWordToSigned w = if i >= bound then i-2*bound else i
  where i = memWordInteger w
        bound = 2^(addrBitSize w-1)

-- | Treat the word as an integer.
memWordInteger :: MemWord w -> Integer
memWordInteger = memWordToUnsigned
{-# DEPRECATED memWordInteger "Use memWordToUnsigned" #-}

-- | Treat the word as a signed integer.
memWordSigned :: MemWidth w => MemWord w -> Integer
memWordSigned = memWordToSigned

-- | Returns number of bits in address.
addrBitSize :: MemWidth w => p w -> Int
addrBitSize w = 8 * addrSize w

instance MemWidth w => Num (MemWord w) where
  MemWord x + MemWord y = memWord $ x + y
  MemWord x - MemWord y = memWord $ x - y
  MemWord x * MemWord y = memWord $ x * y
  abs = id
  fromInteger = memWord . fromInteger
  negate (MemWord x) = memWord (negate x)
  signum (MemWord x) = memWord (signum x)

instance MemWidth w => Bits (MemWord w) where

  MemWord x .&. MemWord y = memWord (x .&. y)
  MemWord x .|. MemWord y = memWord (x .|. y)
  MemWord x `xor` MemWord y = memWord (x `xor` y)
  complement (MemWord x) = memWord (complement x)
  MemWord x `shift` i = memWord (x `shift` i)
  x `rotate` i = addrRotate x i
  bitSize = addrBitSize
  bitSizeMaybe x = Just (addrBitSize x)
  isSigned _ = False
  MemWord x `testBit` i = x `testBit` i
  bit i = memWord (bit i)
  popCount (MemWord x) = popCount x

instance MemWidth w => Enum (MemWord w) where
  toEnum = memWord . fromIntegral
  fromEnum (MemWord x) = fromIntegral x

instance MemWidth w => Real (MemWord w) where
  toRational (MemWord x) = toRational x

instance MemWidth w => Integral (MemWord w) where
  MemWord x `quotRem` MemWord y = (MemWord q, MemWord r)
    where (q,r) = x `quotRem` y
  toInteger (MemWord x) = toInteger x

instance MemWidth w => Bounded (MemWord w) where
  minBound = 0
  maxBound = MemWord (addrWidthMask (Proxy :: Proxy w))

instance MemWidth 32 where
  addrWidthRepr _ = Addr32
  addrWidthMask _ = 0xffffffff
  addrRotate (MemWord w) i =
    MemWord (fromIntegral ((fromIntegral w :: Word32) `rotate` i))
  addrSize _ = 4

instance MemWidth 64 where
  addrWidthRepr _ = Addr64
  addrWidthMask _ = 0xffffffffffffffff
  addrRotate (MemWord w) i = MemWord (w `rotate` i)
  addrSize _ = 8

-- | Number of bytes in an address
addrWidthClass :: AddrWidthRepr w -> (MemWidth w => a) -> a
addrWidthClass Addr32 x = x
addrWidthClass Addr64 x = x

------------------------------------------------------------------------
-- MemInt

-- | A signed integer with the given width.
newtype MemInt (w::Nat) = MemInt { memIntValue :: Int64 }

-- | Convert `Int64` @x@ into mem word @x mod 2^w-1@.
memInt :: forall w . MemWidth w => Int64 -> MemInt w
memInt =
  case addrWidthRepr (Proxy :: Proxy w) of
    Addr32 -> \x -> MemInt (fromIntegral (fromIntegral x :: Int32))
    Addr64 -> \x -> MemInt x

instance Eq (MemInt w) where
  (==) = \x y -> memIntValue x == memIntValue y

instance Ord (MemInt w) where
  compare = \x y -> compare (memIntValue x) (memIntValue y)

instance Hashable (MemInt w) where
  hashWithSalt s (MemInt w) = s `hashWithSalt` w

instance Pretty (MemInt w) where
  pretty = text . show . memIntValue

instance Show (MemInt w) where
  showsPrec p (MemInt i) = showsPrec p i

instance MemWidth w => Bounded (MemInt w) where
  minBound =
    case addrWidthRepr (Proxy :: Proxy w) of
      Addr32 -> MemInt (fromIntegral (minBound :: Int32))
      Addr64 -> MemInt minBound
  maxBound =
    case addrWidthRepr (Proxy :: Proxy w) of
      Addr32 -> MemInt (fromIntegral (maxBound :: Int32))
      Addr64 -> MemInt maxBound

instance MemWidth w => Num (MemInt w) where
  (+) = \x y -> memInt $ memIntValue x + memIntValue y
  (-) = \x y -> memInt $ memIntValue x - memIntValue y
  (*) = \x y -> memInt $ memIntValue x * memIntValue y
  abs = memInt . abs . memIntValue
  fromInteger = memInt . fromInteger
  negate = memInt . negate . memIntValue
  signum = memInt . signum . memIntValue

instance MemWidth w => Enum (MemInt w) where
  toEnum   = memInt . fromIntegral
  fromEnum = fromIntegral . memIntValue

instance MemWidth w => Real (MemInt w) where
  toRational = toRational . memIntValue

instance MemWidth w => Integral (MemInt w) where
  x `quotRem` y = (MemInt q, MemInt r)
    where (q,r) = memIntValue x `quotRem` memIntValue y
  toInteger = toInteger . memIntValue

------------------------------------------------------------------------
-- Relocation

-- | Information about a relocation.  This essentially is a region of
-- memory in a binary whose contents are unknown when the binary is
-- generated.
--
-- For object files, relocations are created for symbol names, as the
-- address they are stored at is assigned by the linker.  The
-- relocation generated by the compiler provides the linker with the
-- information it needs to perform relocations.
--
-- For dynamic executables and shared libraries, relocation values are
-- generated to allow the loader to load the file at a specific address.
-- These may be assigned during loading, or in the case of functions,
-- when first being invoked.
--
-- This structure contains the information needed to compute the value
-- stored in memory, and whether there are constraints on that value.
--
-- The value to be stored in a relocation @r@, is the integer computed by
-- @base + off - rel@ where
--
--  * @base@ is the address of the symbol identified by @relocationSym r@;
--
--  * @off@ is the offset @relocationOffset r@; and
--
--  * @rel@ is the address the relocation is stored at if @relocationIsRel r@
--    is true, and @0@ otherwise.
--
-- The integer value stored is encoded in a bitvector with
-- @relocationSize r@ bytes.  This is interpreted as a signed number
-- using two's complement encoding when @relocationIsSigned r@ is
-- true, and an unsigned number otherwise.  The byte order is
-- determined by @relocationEndiness r@.
--
-- Because the integer value are stored in fixed width bitvectors that
-- cannot represent all legal integer values, the code doing the
-- relocation is not allowed to place symbols at arbitrary addresses.
-- The integer value computed must fit within the given number of
-- bytes, and so relocations effectively are implicit constraints on
-- where code may be stored in memory.
data Relocation w
   = Relocation { relocationSym :: !SymbolIdentifier
                  -- ^ The symbol whose address is used as the base
                  -- of the value to store.
                , relocationOffset :: !(MemWord w)
                  -- ^ A constant value to add to the base
                  -- to compute the relocation
                , relocationIsRel :: !Bool
                  -- ^ If this is true, then the value stored in the relocation
                  -- will be the difference between the relocation symbol and
                  -- offset and the address of the relocation.
                  --
                  -- If false, then the value stored is just the address of the
                  -- symbol plus the offset.
                , relocationSize :: !Int
                  -- ^ Number of bytes in memory that this relocation is
                  -- stored at.
                , relocationIsSigned :: !Bool
                  -- ^ This indicates if the value stored will be
                  -- interpreted as an signed or unsigned number.
                , relocationEndianness :: !Endianness
                  -- ^ The byte order used to encode the relocation in
                  -- memory.
                , relocationJumpSlot :: !Bool
                  -- ^ Returns true if this is a jump slot relocation.
                  --
                  -- This relocation is specifically used for global
                  -- offset table entries, and are typically resolved
                  -- when the function is first called rather than at
                  -- load time.  The address will be initially the
                  -- entry sequence stub, and will be updated once
                  -- resolved by the stub.
                }

-- | Short encoding of endianness for relocation pretty printing
showEnd :: Endianness -> ShowS
showEnd LittleEndian = showString "LE"
showEnd BigEndian = showString "BE"

instance Show (Relocation w) where
  showsPrec _ r =
    showString "[areloc,"
    . shows (relocationSym r)
    . showChar ','
    . showHex (memWordInteger (relocationOffset r))
    . showChar ','
    . shows (8*relocationSize r)
    . (if relocationIsRel r then showString ",PC" else id)
    . (if relocationIsSigned r then showString ",S" else id)
    . showChar ',' . showEnd (relocationEndianness r)
    . showChar ']'

------------------------------------------------------------------------
-- MemChunk

-- | A memory chunk describes a contiguous sequence of bytes within a segment.
--
-- The parameter denotes the width of a memory address.
data MemChunk (w :: Nat)
   = ByteRegion !BS.ByteString
     -- ^ A region with specific bytes
   | RelocationRegion !(Relocation w)
     -- ^ A region whose contents are computed using the expression
     -- denoted by the relocation.
   | BSSRegion !(MemWord w)
     -- ^ A region containing the given number of zero-initialized
     -- bytes.

type SegmentRange = MemChunk
{-# DEPRECATED SegmentRange "Use MemChunk" #-}

ppByte :: Word8 -> String -> String
ppByte w | w < 16    = showChar '0' . showHex w
         | otherwise = showHex w

instance Show (MemChunk w) where
  showsPrec _ (ByteRegion bs)      = \s -> foldr ppByte s (BS.unpack bs)
  showsPrec p (RelocationRegion r) = showsPrec p r
  showsPrec _ (BSSRegion sz)       = showString "[bss," . shows sz . showChar ']'

  showList [] = id
  showList (h : r) = showsPrec 10 h . showList r

------------------------------------------------------------------------
-- SegmentContents

-- | This represents the memory contents in a segment.
newtype SegmentContents w = SegmentContents { segContentsMap :: Map.Map (MemWord w) (MemChunk w) }

chunkSize :: forall w . MemWidth w => MemChunk w -> Word64
chunkSize (ByteRegion bs) = fromIntegral (BS.length bs)
chunkSize (RelocationRegion r) = fromIntegral (relocationSize r)
chunkSize (BSSRegion sz)  = memWordValue sz

contentsSize :: MemWidth w => SegmentContents w -> MemWord w
contentsSize (SegmentContents m) =
  case Map.maxViewWithKey m of
    Nothing -> 0
    Just ((start, c),_) -> memWord (memWordValue start + chunkSize c)

-- | Deconstruct a 'SegmentContents' into its constituent ranges
contentsRanges :: SegmentContents w -> [(MemWord w, MemChunk w)]
contentsRanges = Map.toList . segContentsMap

------------------------------------------------------------------------
-- Presymbol data

-- | Contents of segment/section before symbol folded in.
data PresymbolData = PresymbolData { preBytes :: !BS.ByteString
                                   , preBSS :: !Integer
                                   }

-- | Return number of presymbol bytes remaining
presymbolBytesLeft :: PresymbolData -> Integer
presymbolBytesLeft p = toInteger (BS.length (preBytes p)) + preBSS p

mkPresymbolData :: BS.ByteString -> Integer -> PresymbolData
mkPresymbolData contents0 sz
  | sz < toInteger (BS.length contents0) =
      PresymbolData { preBytes = BS.take (fromInteger sz) contents0
                    , preBSS = 0
                    }
  | otherwise =
      PresymbolData { preBytes = contents0
                    , preBSS = sz - toInteger (BS.length contents0)
                    }

-- | @bssSegment cnt@ creates a BSS region with size @cnt@.
bssSegment :: MemWidth w
           => MemWord w
           -> Integer
           -> [(MemWord w, MemChunk w)]
           -> [(MemWord w, MemChunk w)]
bssSegment o c | c <= 0 = id
               | otherwise = ((o, BSSRegion (fromIntegral c)) :)

-- | Return all segment ranges from remainder of data.
allSymbolData :: MemWidth w
              => MemWord w -- ^ Number of bytes read so far.
              -> PresymbolData
              -> [(MemWord w, MemChunk w)]
              -> [(MemWord w, MemChunk w)]
allSymbolData off (PresymbolData contents bssSize)
  | BS.null contents = bssSegment off bssSize
  | otherwise =
    bssSegment (off + fromIntegral (BS.length contents)) bssSize
      . ((off,  ByteRegion contents) :)


-- | Take the difference between given amount of data out of presymbol data.
splitSegment :: MemWidth w
             => MemWord w -- ^ Base address of segment
             -> [(MemWord w, MemChunk w)] -- ^ Symbols added so far.
             -> MemWord w -- ^ Current address
             -> MemWord w -- ^ Target address (can assume at least target addresss
             -> PresymbolData
             -> ([(MemWord w, MemChunk w)], PresymbolData)
splitSegment _baseAddr pre curAddr targetAddr dta
  | targetAddr < curAddr = error "TargetAddress less that curAddr"
  | targetAddr == curAddr = (pre, dta)
splitSegment baseAddr pre curAddr targetAddr (PresymbolData contents bssSize)
   -- Case where relocation is contained within regular contents
  | toInteger cnt <= toInteger (BS.length contents) =
    ( (curAddr - baseAddr, ByteRegion (BS.take (fromIntegral cnt) contents)) : pre
    , PresymbolData (BS.drop (fromIntegral cnt) contents) bssSize
    )
  -- If contents is empty, then we just have BSS.
  | BS.null contents =
      if bssSize < toInteger (targetAddr - curAddr) then
        error "Out of bytes"
      else
        ( (curAddr - baseAddr, BSSRegion cnt) : pre
        , PresymbolData BS.empty (bssSize - toInteger cnt)
        )
  -- We take all of file-based data and at least some BSS.
  | otherwise =
      ( [ ( curAddr - baseAddr + fromIntegral (BS.length contents)
          , BSSRegion (cnt - fromIntegral (BS.length contents))
          )
        , (curAddr - baseAddr, ByteRegion contents)
        ] ++ pre
      , PresymbolData BS.empty (bssSize - (toInteger cnt - toInteger (BS.length contents)))
      )
 where cnt = targetAddr - curAddr

-- | @dropSegment cnt dta@ drops @cnt@ bytes from @dta@.
dropSegment :: Int -> PresymbolData -> PresymbolData
dropSegment cnt (PresymbolData contents bssSize)
  | cnt <= BS.length contents = PresymbolData (BS.drop cnt contents) bssSize
  | otherwise = PresymbolData BS.empty (bssSize - toInteger (cnt - BS.length contents))

-- | Return the given bytes
takePresymbolBytes :: Int -> PresymbolData -> Maybe BS.ByteString
takePresymbolBytes cnt p
  | toInteger cnt  <= presymbolBytesLeft p =
      Just $ BS.take cnt (preBytes p)
          <> BS.replicate (cnt - BS.length (preBytes p)) 0
  | otherwise =
      Nothing


------------------------------------------------------------------------
-- Relocation processing

-- | Function for resolving the new contents of a relocation entry given an optional
-- index for the current segment and the existing contents.
--
-- The segment index is used for dynamic relocations and set to
-- `Nothing` for static relocations.
type ResolveFn m w = Maybe SegmentIndex -> BS.ByteString -> m (Maybe (Relocation w))

-- | Information about a relocation sufficient to know how many bytes
-- are affected, and how to replaces the existing bytes.
data RelocEntry m w = RelocEntry { relocEntrySize :: !(MemWord w)
                                   -- ^ Number of bytes in relocation
                                 , applyReloc :: !(ResolveFn m w)
                                 }

-- | This takes a list of symbols and an address and coerces into a memory contents.
--
-- If the size is different from the length of file contents, then the file content
-- buffer is truncated or zero-extended as in a BSS.
applyRelocsToBytes :: (Monad m, MemWidth w)
                   => MemWord w
                      -- ^ Virtual offset of segment.
                   -> Maybe SegmentIndex
                   -- ^ Identifier for this segment in relocation if this is created from so/exe.
                   -> [(MemWord w, MemChunk w)]
                      -- ^ Chunks so far.
                   -> MemWord w
                      -- ^ Current virtual address (must be greater than linkBaseOff)
                   -> [(MemWord w, RelocEntry m w)]
                      -- ^ List of relocations to process in order.
                      -- Each offset should be at offset.
                   -> PresymbolData
                   -- ^ The remaining bytes in memory including
                   -- a number extra bss.
                   -> m (SegmentContents w)
applyRelocsToBytes baseAddr msegIdx pre ioff ((addr,v):rest) buffer
  -- We only consider relocations that are in the range of this segment,
  -- so we require the difference between the address and baseAddr is
  -- less than regionSize
  | addr < ioff = error "Encountered overlapping relocations."
    -- Check start of relocation is in range.
  | toInteger (addr - ioff) < presymbolBytesLeft buffer  = do

      let (preRelocChunks, atRelocContents) = splitSegment baseAddr pre ioff addr buffer
      -- Get relocation size.
      let rsz = relocEntrySize v
      case takePresymbolBytes (fromIntegral rsz) atRelocContents of
        Nothing -> do
          error $ "Relocation at " ++ show addr ++ " needs "
                  ++ show rsz ++ " bytes, but only " ++ show (presymbolBytesLeft atRelocContents)
                  ++ " bytes remaining."
        Just bytes -> do
          mr <- applyReloc v msegIdx bytes
          case mr of
            Just r -> do
              -- Get number of bytes between this address offset and the current offset."
              let pre' = (addr - baseAddr,  RelocationRegion r): preRelocChunks
              let post = dropSegment (fromIntegral rsz) atRelocContents
              applyRelocsToBytes baseAddr msegIdx pre' (addr + rsz) rest post
            Nothing -> do
              -- Skipping relocation
              applyRelocsToBytes baseAddr msegIdx pre ioff rest buffer
applyRelocsToBytes baseAddr _ pre ioff _ buffer =
  pure $ SegmentContents $ Map.fromDescList $
    allSymbolData (ioff - baseAddr) buffer pre

------------------------------------------------------------------------
-- MemSegment

-- | This is an identifier used to support relocatable code.
--
-- Memory segments with absolute addresses should use a region index
-- of `0`.  Non-zero region indices Absolute segments have a base index of zero, and non-zero values correspond
type RegionIndex = Int

-- | Information about a contiguous sequence of bytes in memory.
--
-- Our memory model supports relocatable code, and so segments may
-- have either fixed or floating addresses.  Floating addresses are
-- themselves represented as the offset of a base address which is
-- identified by the `segmentBase` which is `0` for segments with
-- absolute addresses and non-zero oitherwise.  Binaries may have
-- floating segments that are fixed relative to each other, and this
-- can be modeled by creating different segments with the same
-- non-zero `segmentBase` identifier.
data MemSegment w
   = MemSegment { segmentBase  :: !RegionIndex
                  -- ^ Base for this segment
                  --
                  -- N.B. 0 indicates a fixed base address of zero.
                , segmentOffset :: !(MemWord w)
                  -- ^ Offset of segment relative to segmentBase
                , segmentFlags :: !Perm.Flags
                                  -- ^ Permission flags
                , segmentContents :: !(SegmentContents w)
                                     -- ^ Map from offsets to the contents of
                                     -- the segment.
                }

instance Eq (MemSegment w) where
  x == y = segmentBase   x == segmentBase y
        && segmentOffset x == segmentOffset y

instance Ord (MemSegment w) where
  compare x y
    =  compare (segmentBase x)   (segmentBase y)
    <> compare (segmentOffset x) (segmentOffset y)

-- | This creates a memory segment from a buffer after applying
-- relocations and options for
memSegment :: forall m w
           .  (Monad m, MemWidth w)
           => Map (MemWord w) (RelocEntry m w)
              -- ^ Map from region offset to relocation entry for segment.
           -> RegionIndex
              -- ^ Index of base (0=absolute address)
           -> Integer
              -- ^ Offset to add to linktime address for this segment.
           -> Maybe SegmentIndex
              -- ^ Identifier for this segment in relocation if this is created from so/exe.
           -> MemWord w
              -- ^ Linktime address of segment.
           -> Perm.Flags
              -- ^ Permissions for segment.
           -> BS.ByteString
           -- ^ File contents for segment.
           -> MemWord w
           -- ^ Expected size (must be positive)
           -> m (MemSegment w)
memSegment relocMap regionIndex regionOff msegIdx linkBaseOff flags bytes sz
      -- Return nothing if size is not positive
    | not (sz > 0) = error $ "Memory segments must have a positive size."
      -- Make sure end of segment does not overflow.
    | regionOff + toInteger linkBaseOff + toInteger sz > toInteger (maxBound :: MemWord w) =
      error "Contents too large for base."
    | otherwise = do
      let symbolPairs :: [(MemWord w, RelocEntry m w)]
          symbolPairs
            = Map.toList
            $ Map.dropWhileAntitone (< linkBaseOff) relocMap

      contents <- applyRelocsToBytes linkBaseOff msegIdx [] linkBaseOff symbolPairs
                    (mkPresymbolData bytes (toInteger sz))
      let off = fromInteger regionOff + linkBaseOff
      pure $! MemSegment { segmentBase = regionIndex
                         , segmentOffset = off
                         , segmentFlags = flags
                         , segmentContents = contents
                         }

-- | Return the size of the segment data.
segmentSize :: MemWidth w => MemSegment w -> MemWord w
segmentSize = contentsSize . segmentContents

-- | Pretty print a memory segment.
ppMemSegment :: MemWidth w => MemSegment w -> Doc
ppMemSegment s =
  indent 2 $ vcat [ text "base   =" <+> text (show (segmentBase s))
                  , text "offset =" <+> text (show (segmentOffset s))
                  , text "flags  =" <+> text (show (segmentFlags s))
                  , text "size   =" <+> text (show (segmentSize s))
                  ]

instance MemWidth w => Show (MemSegment w) where
  show = show . ppMemSegment

------------------------------------------------------------------------
-- MemSegmentOff

-- | A pair containing a segment and offset.
--
-- Functions that return a segment-offset pair enforce that the offset
-- is strictly less than the size of the memory segment in bytes.
data MemSegmentOff w = MemSegmentOff { segoffSegment :: !(MemSegment w)
                                       -- ^ The segment this is an offset of
                                     , segoffOffset :: !(MemWord w)
                                       -- ^ The offset within the segment.
                                     }
  deriving (Eq, Ord)

------------------------------------------------------------------------
-- Memory

-- | Map from region index to map of offset to segment.
type SegmentOffsetMap w = Map.Map RegionIndex (Map.Map (MemWord w) (MemSegment w))

-- | A datatype for describing the potential memory layout of binaries
-- during execution.
--
-- This datatype abstracts aways the details of the executable file
-- format to provide an abstraction that is intended to support
-- different architectures and executable/object file formats.
--
-- This does not represent memory once loading is complete, but rather
-- provide a pre-loader perspective.  As such, it supports a more
-- complex notion of addresses to accomodate relocatable binaries
-- where the precise location of code or data is not known, but one
-- may have relative offsets for the information.
--
-- The memory model assumes that the set of legal addresses are sparse,
-- and have read/write/executable bit permissions associated with them.
-- Different contiguous regions may not have known fixed addresses, but
-- may have fixed relative offsets.
--
-- To support this, the memory representation supports relocatable
-- regions.  Each region is defined by an index, and multiple segments
-- may be relative to the same index.  The index `0` is reserved to
-- denote absolute addresses, while the other regions may have other
-- addresses.
--
-- Region indices may not correspond precisely with segments or
-- section indices within the binary, and so our memory model also
-- maintains mappings so that one can map both sections and segments
-- in the binary to the address it is loaded at.
data Memory w = Memory { memAddrWidth :: !(AddrWidthRepr w)
                         -- ^ Return the address width of the memory
                       , memSegmentMap :: !(SegmentOffsetMap w)
                         -- ^ Segment map
                       , memSectionIndexMap :: !(Map SectionIndex (MemSegmentOff w))
                         -- ^ Map from registered section indices to the segment offset it is loaded at.
                       , memSegmentIndexMap  :: !(Map SegmentIndex (MemSegment w))
                         -- ^ Map from registered segment indices to associated segment.
                       , memBaseAddr :: !(Maybe (MemAddr w))
                         -- ^ This denotes the base region for loads.
                       }

-- | Return the set of memory segments in memory.
memSegments :: Memory w -> [MemSegment w]
memSegments m = concatMap Map.elems (Map.elems (memSegmentMap m))

instance MemWidth w => Show (Memory w) where
  show = show . memSegments

-- | Return the number of bytes in an address.
memWidth :: Memory w -> NatRepr w
memWidth = addrWidthNatRepr . memAddrWidth

-- | Add a new section index to address entry.
memBindSectionIndex :: SectionIndex -> MemSegmentOff w -> Memory w -> Memory w
memBindSectionIndex idx addr mem
  | Map.member idx (memSectionIndexMap mem) =
      error $ "memBindSectionIndex: duplicate index " ++ show idx
  | otherwise =
      mem { memSectionIndexMap = Map.insert idx addr (memSectionIndexMap mem) }

-- | Record binding from the segment index to the segment.
memBindSegmentIndex :: SegmentIndex -> MemSegment w -> Memory w -> Memory w
memBindSegmentIndex idx seg mem
  | Map.member idx (memSegmentIndexMap mem) =
      error $ "memBindSegmentIndex: duplicate index " ++ show idx
  | otherwise =
      mem { memSegmentIndexMap = Map.insert idx seg (memSegmentIndexMap mem) }

-- | Set the region index used or the load addresses.
memSetBaseAddr :: MemAddr w -> Memory w -> Memory w
memSetBaseAddr r m = m { memBaseAddr = Just r }

-- | A memory with no segments.
emptyMemory :: AddrWidthRepr w -> Memory w
emptyMemory w = Memory { memAddrWidth       = w
                       , memSegmentMap      = Map.empty
                       , memSectionIndexMap = Map.empty
                       , memSegmentIndexMap = Map.empty
                       , memBaseAddr        = Nothing
                       }

-- | Return segments with executable permissions.
executableSegments :: Memory w -> [MemSegment w]
executableSegments = filter (Perm.isExecutable . segmentFlags) . memSegments
{-# DEPRECATED executableSegments "Use filter (Perm.isExecutable . segmentFlags) . memSegments." #-}

-- | Return segments with read-only permissions.
readonlySegments :: Memory w -> [MemSegment w]
readonlySegments = filter (Perm.isReadonly . segmentFlags) . memSegments
{-# DEPRECATED readonlySegments "Filter memSegments directly." #-}

-- | Describes why we could not insert segment into memory.
data InsertError w
   = OverlapSegment (MemSegment w) (MemSegment w)
     -- ^ The inserted segment overlaps with the given segment.

-- | Print description of insertion error.
showInsertError :: InsertError w -> String
showInsertError (OverlapSegment _base _seg) = "overlaps with memory segment."

-- | Insert segment into memory or fail if this overlaps with another
-- segment in memory.
insertMemSegment :: MemSegment w
                 -> Memory w
                 -> Either (InsertError w) (Memory w)
insertMemSegment seg mem = addrWidthClass (memAddrWidth mem) $ do
  let segOffMap = memSegmentMap mem
  let base = segmentBase seg
      m = Map.findWithDefault Map.empty base segOffMap
  case Map.lookupGE (segmentOffset seg) m of
    Just (next,old) | next < segmentOffset seg + segmentSize seg ->
     Left $ OverlapSegment seg old
    _ -> do
      let absMap = Map.insert base (Map.insert (segmentOffset seg) seg m) segOffMap
      pure $ mem { memSegmentMap = absMap }

------------------------------------------------------------------------
-- MemAddr

-- | An address in memory.  Due to our use of relocatable "regions",
-- this internally represented by a region index for the base, and an
-- offset.
--
-- This representation does not require that the address is mapped to
-- actual memory (see `MemSegmentOff` for an address representation
-- that ensures the reference points to allocated memory).
data MemAddr w
   = MemAddr { addrBase :: {-# UNPACK #-} !RegionIndex
             , addrOffset :: {-# UNPACK #-} !(MemWord w)
             }
     -- ^ An address formed from a specific value.
  deriving (Eq, Ord)

instance Hashable (MemAddr w) where
  hashWithSalt s a = s `hashWithSalt` addrBase a  `hashWithSalt` addrOffset a

instance Show (MemAddr w) where
  showsPrec _ (MemAddr 0 a) = shows a
  showsPrec p (MemAddr i off) =
    showParen (p > 6)
    $ showString "segment"
    . shows i
    . showString "+"
    . shows off

instance Pretty (MemAddr w) where
  pretty = text . show

-- | Given an absolute address, this returns a segment and offset into the segment.
absoluteAddr :: MemWord w -> MemAddr w
absoluteAddr o = MemAddr { addrBase = 0, addrOffset = o }

-- | Construct an address from the offset of a memory segment.
segmentOffAddr :: MemWidth w => MemSegment w -> MemWord w -> MemAddr w
segmentOffAddr seg off = MemAddr { addrBase = segmentBase seg, addrOffset = segmentOffset seg + off }

-- | Construct an address relative to an existing memory segment.
relativeAddr :: MemWidth w => MemSegment w -> MemWord w -> MemAddr w
relativeAddr = segmentOffAddr
{-# DEPRECATED relativeAddr "Use segmentOffAddr" #-}

-- | Return an absolute address if the region of the memAddr is 0.
asAbsoluteAddr :: MemWidth w => MemAddr w -> Maybe (MemWord w)
asAbsoluteAddr (MemAddr i w) = if i == 0 then Just w else Nothing

-- | Clear the least significant bit of an address.
clearAddrLeastBit :: MemAddr w -> MemAddr w
clearAddrLeastBit (MemAddr i (MemWord off)) = MemAddr i (MemWord (off .&. complement 1))

-- | Return True if least-significant bit in addr is set.
addrLeastBit :: MemAddr w -> Bool
addrLeastBit (MemAddr _ (MemWord off)) = off `testBit` 0

-- | Increment an address by a fixed amount.
incAddr :: MemWidth w => Integer -> MemAddr w -> MemAddr w
incAddr o a = a { addrOffset = addrOffset a + fromInteger o }

-- | Returns the number of bytes between two addresses if they point to
-- the same region and `Nothing` if they are different segments.
diffAddr :: MemWidth w => MemAddr w -> MemAddr w -> Maybe Integer
diffAddr (MemAddr xb xoff) (MemAddr yb yoff)
  | xb == yb = Just $ toInteger xoff - toInteger yoff
  | otherwise = Nothing

------------------------------------------------------------------------
-- MemSegmentOff operations

-- | Return the number of bytes in the segment after this address.
segoffBytesLeft :: MemWidth w => MemSegmentOff w -> Integer
segoffBytesLeft segOff = sz - off
  where sz = toInteger (segmentSize (segoffSegment segOff))
        off = toInteger (segoffOffset segOff)

-- | Make a segment offset pair after ensuring the offset is valid
resolveSegmentOff :: MemWidth w => MemSegment w -> MemWord w -> Maybe (MemSegmentOff w)
resolveSegmentOff seg off
  | off < segmentSize seg = Just MemSegmentOff { segoffSegment = seg, segoffOffset = off }
  | otherwise = Nothing

-- | Return the segment offset associated with the given region offset if any.
resolveRegionOff :: Memory w -> RegionIndex -> MemWord w -> Maybe (MemSegmentOff w)
resolveRegionOff mem idx addr = addrWidthClass (memAddrWidth mem) $ do
  m <- Map.lookup idx (memSegmentMap mem)
  (base, seg) <- Map.lookupLE addr m
  resolveSegmentOff seg (addr - base)

-- | Return the segment offset associated with the given region offset if any.
resolveAddr :: Memory w -> RegionIndex -> MemWord w -> Maybe (MemSegmentOff w)
resolveAddr = resolveRegionOff
{-# DEPRECATED resolveAddr "Use resolveRegionOff" #-}

-- | Return the address of a segment offset.
segoffAddr :: MemSegmentOff w -> MemAddr w
segoffAddr (MemSegmentOff seg off) =
  MemAddr { addrBase = segmentBase seg
            -- Segment off
          , addrOffset = MemWord $ memWordValue (segmentOffset seg) + memWordValue off
          }

-- | Return the segment associated with the given address if well-defined.
resolveAbsoluteAddr :: Memory w -> MemWord w -> Maybe (MemSegmentOff w)
resolveAbsoluteAddr mem addr = resolveRegionOff mem 0 addr

-- | Return the absolute address associated with the segment offset pair (if any)
segoffAsAbsoluteAddr :: MemWidth w => MemSegmentOff w -> Maybe (MemWord w)
segoffAsAbsoluteAddr mseg = do
  let seg = segoffSegment mseg
   in if segmentBase seg == 0 then
        -- We do not need to normalize, because the overflow was checked when the segment offset
        -- was created.
        Just $! MemWord (memWordValue (segmentOffset seg) + memWordValue (segoffOffset mseg))
       else
        Nothing

-- | Return the absolute address associated with the segment offset pair (if any)
msegAddr :: MemWidth w => MemSegmentOff w -> Maybe (MemWord w)
msegAddr = segoffAsAbsoluteAddr
{-# DEPRECATED msegAddr "Use segoffAsAbsoluteAddr" #-}

-- | Clear the least-significant bit of an segment offset.
clearSegmentOffLeastBit :: MemWidth w => MemSegmentOff w -> MemSegmentOff w
clearSegmentOffLeastBit (MemSegmentOff seg off) = MemSegmentOff seg (off .&. complement 1)

-- | Increment a segment offset by a given amount.
--
-- Returns 'Nothing' if the result would be out of range.
incSegmentOff :: MemWidth w => MemSegmentOff w -> Integer -> Maybe (MemSegmentOff w)
incSegmentOff (MemSegmentOff seg off) inc
  | 0 <= next && next <= toInteger (segmentSize seg) =
      Just $ MemSegmentOff seg (fromInteger next)
  | otherwise = Nothing
  where next = toInteger off + inc

-- | Return the difference between two segment offsets pairs or `Nothing` if undefined.
diffSegmentOff :: MemWidth w => MemSegmentOff w -> MemSegmentOff w -> Maybe Integer
diffSegmentOff (MemSegmentOff xseg xoff) (MemSegmentOff yseg yoff)
  | segmentBase xseg == segmentBase yseg =
    Just $ toInteger (segmentOffset xseg + xoff) - toInteger (segmentOffset yseg + yoff)
  | otherwise = Nothing

instance MemWidth w => Show (MemSegmentOff w) where
  showsPrec p (MemSegmentOff seg off) =
    if segmentBase seg == 0 then
      showString "0x" . showHex (segmentOffset seg + off)
     else
       showParen (p > 6)
        $ showString "segment"
        . shows (segmentBase seg)
        . showString "+"
        . shows (segmentOffset seg + off)

instance MemWidth w => Pretty (MemSegmentOff w) where
  pretty = text . show

-- | This walks through all the memory regions and looks at each
-- address size block of memory that is aligned at a multiple of the
-- address size.
--
-- It returns a list of all offset and value pairs that can be
-- interpreted as a valid offset within a memory segment.
memAsAddrPairs :: Memory w
               -> Endianness
               -> [(MemSegmentOff w, MemSegmentOff w)]
memAsAddrPairs mem end = addrWidthClass (memAddrWidth mem) $ do
  seg <- memSegments mem
  (contentsOffset,r) <- contentsRanges (segmentContents seg)
  let sz :: Int
      sz = addrSize mem
  case r of
    ByteRegion bs -> do
      -- Split bytes into sequence of pairs with offset and value.
      (byteOff,w) <-
        zip [contentsOffset,contentsOffset+fromIntegral sz..]
            (regularChunks sz bs)
      -- Attempt to read bytes as a valid segment offset.
      let Just val = addrRead end w
      case resolveAbsoluteAddr mem val of
        Just segOffVal ->
          [(MemSegmentOff seg byteOff, segOffVal)]
        Nothing ->
          []
    RelocationRegion{} -> []
    BSSRegion{} -> []

------------------------------------------------------------------------
-- SegmentOff deprecated

-- | Return segment this is offset of.
msegSegment :: MemSegmentOff w -> MemSegment w
msegSegment = segoffSegment
{-# DEPRECATED msegSegment "Use segoffSegment" #-}

-- | Return offset of segment
msegOffset :: MemSegmentOff w -> MemWord w
msegOffset = segoffOffset
{-# DEPRECATED msegOffset "Use segoffOffset" #-}

-- | Return the number of bytes in the segment after this address.
msegByteCountAfter :: MemWidth w => MemSegmentOff w -> Integer
msegByteCountAfter = segoffBytesLeft
{-# DEPRECATED msegByteCountAfter "Use segoffBytesLeft" #-}

-- | Convert the segment offset to an address.
relativeSegmentAddr :: MemWidth w => MemSegmentOff w -> MemAddr w
relativeSegmentAddr = segoffAddr
{-# DEPRECATED relativeSegmentAddr "Use segoffAddr" #-}

-- | Return a segment offset from the address if defined.
asSegmentOff :: Memory w -> MemAddr w -> Maybe (MemSegmentOff w)
asSegmentOff mem (MemAddr i addr) = resolveAddr mem i addr

------------------------------------------------------------------------
-- MemoryError

-- | Type of errors that may occur when reading memory.
data MemoryError w
   = AccessViolation !(MemAddr w)
     -- ^ Memory could not be read, because it was not defined.
   | PermissionsError !(MemAddr w)
     -- ^ Memory could not be read due to insufficient permissions.
   | UnexpectedRelocation !(MemAddr w) !(Relocation w)
     -- ^ Read from location that partially overlaps a relocated entry
   | UnexpectedByteRelocation !(MemAddr w) !(Relocation w)
     -- ^ An relocation appeared when reading a byte.
   | Unsupported32ImmRelocation !(MemAddr w) !(Relocation w)
     -- ^ An unsupported relocation appeared when reading a 32-bit immediate.
   | UnsupportedJumpOffsetRelocation !(MemAddr w) !(Relocation w)
     -- ^ An unsupported relocation appeared when reading a jump offset.
   | UnexpectedBSS !(MemAddr w)
     -- ^ We unexpectedly encountered a BSS segment/section.
   | InvalidAddr !(MemAddr w)
     -- ^ The data at the given address did not refer to a valid memory location.
   | InvalidRead !(MemSegmentOff w) !Word64
     -- ^ Can't read the given number of bytes from the offset as that is outside
     -- allocated memory.

instance MemWidth w => Show (MemoryError w) where
  show err =
    case err of
      AccessViolation a ->
        "Access violation at " ++ show a ++ "."
      PermissionsError a ->
        "Insufficient permissions at " ++ show a ++ "."
      UnexpectedRelocation a r ->
        "Attempt to read an unexpected relocation entry at " ++ show a ++ ":\n"
        ++ "  " ++ show r
      UnexpectedByteRelocation a r ->
        "Attempt to read a relocation as a byte at " ++ show a ++ ":\n"
        ++ "  " ++ show r
      Unsupported32ImmRelocation a r ->
        "Attempt to read an unsupported relocation as a 32-bit immediate at " ++ show a ++ ":\n"
        ++ "  " ++ show r
      UnsupportedJumpOffsetRelocation a r ->
        "Attempt to read an unsupported relocation as a jump offset at " ++ show a ++ ":\n"
        ++ "  " ++ show r
      UnexpectedBSS a ->
        "Attempt to read zero initialized BSS memory at " ++ show a ++ "."
      InvalidAddr a ->
        "Attempt to interpret an invalid address: " ++ show a ++ "."
      InvalidRead a c ->
        "Read " ++ show c ++ " bytes if after defined memory " ++ show a ++ "."

------------------------------------------------------------------------
-- Reading contents

-- | Return list of contents from given word or an error if this we can't cleanly
-- partition a relocation
-- due to a relocation.
segoffContentsAfter :: MemWidth w
                    => MemSegmentOff w
                    -> Either (MemoryError w) [MemChunk w]
segoffContentsAfter mseg = do
  -- Get offset within segment to get
  let off = segoffOffset mseg
  -- Get complete contents of segment
  let contents = segmentContents (segoffSegment mseg)
  -- Split the map into all segments starting strictly before offset,
  -- memory starting at offset (if any), and contents strictly after offset.
  let (premap,mv,post) = Map.splitLookup off (segContentsMap contents)
  case mv of
    -- If something starts at offset, then return it and everything after.
    Just v -> Right $ v : Map.elems post
    -- If no memory starts exactly at offset, then
    -- look at the last segment starting before offset.
    Nothing ->
      case Map.maxViewWithKey premap of
        -- This implies nothing starts before the segment offset, which should not be
        -- allowed
        Nothing -> error $ "Memory.segoffContentsAfter invalid contents"
        -- If last segment is a byte region then we drop elements before offset.
        Just ((preOff, ByteRegion bs),_) -> do
          let v = ByteRegion (BS.drop (fromIntegral (off - preOff)) bs)
          Right $ v : Map.elems post
        -- If last segment is a BSS region, then we drop elements before offset.
        Just ((preOff, BSSRegion sz),_) -> do
          let v = BSSRegion (sz - fromIntegral (off - preOff))
          Right $ v : Map.elems post
        -- If last segment is a symbolic reference, then the code is asking
        -- us to partition a symbolic reference in two, which we cannot do.
        Just ((_, RelocationRegion r),_) ->
          Left $ UnexpectedRelocation (relativeSegmentAddr mseg) r

contentsAfterSegmentOff :: MemWidth w
                        => MemSegmentOff w
                        -> Either (MemoryError w) [MemChunk w]
contentsAfterSegmentOff = segoffContentsAfter
{-# DEPRECATED contentsAfterSegmentOff "Use segoffContentsAfter" #-}

------------------------------------------------------------------------
-- Split segment range list.

-- | @forcedTakeMemChunks ranges cnt@ attempts to read @cnt@ bytes from
-- @ranges@.
--
-- It is a total function, and will return @ranges@ if it contains
-- less than @cnt@ bytes.  It may also return more than @cnt@ bytes as
-- if a relocation region spans across the break, it will return the
-- region.
forcedTakeMemChunks :: forall w
                  .  MemWidth w => [MemChunk w] -> MemWord w -> [MemChunk w]
forcedTakeMemChunks _ 0 = []
forcedTakeMemChunks rngs c = do
  let rest :: [MemChunk w] -> MemWord w -> [MemChunk w]
      rest l d | c > d = forcedTakeMemChunks l (c - d)
               | otherwise = []
  case rngs of
    [] -> []
    ByteRegion b : l ->
      ByteRegion (BS.take (fromIntegral c) b)
      : rest l (fromIntegral (BS.length b))
    RelocationRegion r : l ->
      RelocationRegion r
      : rest l (fromIntegral (relocationSize r))
    BSSRegion d : l ->
      BSSRegion (min d c)
      : rest l d

takeSegmentPrefix :: forall w
                  .  MemWidth w => [MemChunk w] -> MemWord w -> [MemChunk w]
takeSegmentPrefix = forcedTakeMemChunks
{-# DEPRECATED takeSegmentPrefix "Use forcedTakeMemChunks" #-}


-- | Describes why we could not split the memory chunks.
data SplitError w
   = SplitUnexpectedRelocation !(Relocation w)
     -- ^ A relocation was right in the middle of where we tried to split chunks.
   | SplitInvalidAddr
     -- ^ The byte count to split at was longer than the number of chunks.

-- | Convert `SplitError` to equivalent `MemoryError`.
--
-- Note. External code does not use this, so unless we get feedback
-- otherwise, it will be dropped in a future Macaw release.
dropErrorAsMemError :: MemAddr w -> SplitError w -> MemoryError w
dropErrorAsMemError a (SplitUnexpectedRelocation r) = UnexpectedRelocation a r
dropErrorAsMemError a SplitInvalidAddr = InvalidAddr a

{-# DEPRECATED dropErrorAsMemError "dropErrorAsMemError is not being used by the rest of Macaw, and a candidate for deletion." #-}

splitMemChunks' :: MemWidth w
                       => [MemChunk w]
                       -> Int
                       -> [MemChunk w]
                       -> Either (SplitError w) ([MemChunk w], [MemChunk w])
splitMemChunks' prev c next
  | c <= 0 = Right (reverse prev, next)
splitMemChunks' _ _ [] = Left SplitInvalidAddr
splitMemChunks' prev cnt (reg@(ByteRegion bs) : rest) = do
  let sz = BS.length bs
  if cnt < sz then do
    let taken   = ByteRegion (BS.take cnt bs):prev
    let dropped = ByteRegion (BS.drop cnt bs) : rest
    pure $ (reverse taken, dropped)
   else do
    splitMemChunks' (reg:prev) (cnt - sz) rest
splitMemChunks' prev cnt (reg@(RelocationRegion r):rest) = do
  let sz = relocationSize r
  if toInteger cnt < toInteger sz then
    Left (SplitUnexpectedRelocation r)
   else do
    splitMemChunks' (reg:prev) (cnt - fromIntegral sz) rest
splitMemChunks' prev cnt (reg@(BSSRegion sz): rest) =
  if toInteger cnt < toInteger sz then do
    let taken   = BSSRegion (fromIntegral cnt):prev
    let dropped = BSSRegion (sz - fromIntegral cnt) : rest
    pure $ (reverse taken, dropped)
   else
    splitMemChunks' (reg:prev) (cnt - fromIntegral sz) rest

-- | Given a contiguous sequence of memory chunks and a number of
-- bytes `c`, this partitions the data in two data regions.  The first
-- contains the first `c` bytes in the data; the second contains the
-- rest of the data.
--
-- This will return an error if the size of the data is too small
-- or the partition would split a relocation entry.
splitMemChunks :: MemWidth w
               => [MemChunk w]
               -> Int
               -> Either (SplitError w) ([MemChunk w], [MemChunk w])
splitMemChunks l c = splitMemChunks' [] c l

-- | Given a segment data and a number of bytes `c`, this partitions the data in
-- two data regions.  The first contains the first `c` bytes in the data; the second
-- contains the rest of the data.
--
-- This will return an exception if the size of the data is too small or the partition
-- would split a relocation entry.
splitSegmentRangeList :: MemWidth w
                      => [MemChunk w]
                      -> Int
                      -> Either (SplitError w) ([MemChunk w], [MemChunk w])
splitSegmentRangeList = splitMemChunks
{-# DEPRECATED splitSegmentRangeList "Use splitMemChunks" #-}


-- | Given a contiguous list of segment ranges and a number of bytes to drop, this
-- returns the remaining segment ranges or throws an error.
dropSegmentRangeListBytes :: forall w
                          .  MemWidth w
                          => [MemChunk w]
                          -> Int
                          -> Either (SplitError w) [MemChunk w]
dropSegmentRangeListBytes l c = snd <$> splitMemChunks l c
{-# DEPRECATED dropSegmentRangeListBytes "Use splitMemChunks" #-}

------------------------------------------------------------------------
-- Memory reading utilities

-- | This resolves a memory address into a segment offset pair if it
-- points to a valid pair.
resolveMemAddr :: Memory w -> MemAddr w -> Either (MemoryError w) (MemSegmentOff w)
resolveMemAddr mem addr =
  case asSegmentOff mem addr of
    Just p -> Right p
    Nothing -> Left (InvalidAddr addr)

-- | Return contents starting from location or throw a memory error if there
-- is an unaligned relocation.
addrContentsAfter :: Memory w
                  -> MemAddr w
                  -> Either (MemoryError w) [MemChunk w]
addrContentsAfter mem addr = do
  addrWidthClass (memAddrWidth mem) $
    segoffContentsAfter =<< resolveMemAddr mem addr

-- | Attempt to read a bytestring of the given length
readByteString' :: RegionIndex
                   -- ^ Region we are in.
                -> BS.ByteString
                   -- ^ Bytestring read so far.
                -> Word64
                   -- ^ Bytes read so far.
                -> [MemChunk w]
                  -- ^ Remaining memory chunks to read from.
                -> Word64
                   -- ^ Total remaining number of bytes to read.
                -> Either (MemoryError w) BS.ByteString
readByteString' _ prev _ _ 0 =
  pure $! prev
readByteString' _ _ _ [] _ = error "internal: readByteString' given too many bytes."
readByteString' reg prev off (ByteRegion bs:rest) cnt = do
  let sz = fromIntegral (BS.length bs)
  if cnt <= sz then
    pure $! prev <> BS.take (fromIntegral cnt) bs
   else do
    let off' = off + sz
    let cnt' = cnt - sz
    seq cnt' $ seq off' $ readByteString' reg (prev <> bs) off' rest cnt'
readByteString' reg _ off (RelocationRegion r:_) _ = do
  let addr = MemAddr { addrBase = reg, addrOffset = MemWord off }
  Left $! UnexpectedRelocation addr r
readByteString' reg prev off (BSSRegion sz0:rest) cnt = do
  let sz :: Word64
      sz = memWordValue sz0
  if cnt <= sz then do
    when (cnt > fromIntegral (maxBound :: Int)) $ do
      error $ "Illegal size " ++ show cnt
    pure $! prev <> BS.replicate (fromIntegral cnt) 0
   else do
    when (sz > fromIntegral (maxBound :: Int)) $ do
      error $ "Illegal size " ++ show cnt
    let bs = BS.replicate (fromIntegral sz) 0
    let off' = off + sz
    let cnt' = cnt - sz
    seq cnt' $ seq off' $ readByteString' reg (prev <> bs) off' rest cnt'

-- | Attempt to read a bytestring of the given length
readByteString :: Memory w
               -> MemAddr w
               -> Word64 -- ^ Number of bytes to read
               -> Either (MemoryError w) BS.ByteString
readByteString mem addr cnt = addrWidthClass (memAddrWidth mem) $ do
  segOff <- resolveMemAddr mem addr
  -- Check read is in range.
  when (toInteger cnt > segoffBytesLeft segOff) $ do
    Left $! InvalidRead segOff cnt
  -- Get contents after segment
  l      <- segoffContentsAfter segOff
  readByteString' (addrBase addr) BS.empty (memWordValue (addrOffset addr)) l cnt

-- | Read an address from the value in the segment or report a memory
-- error.
readAddr :: Memory w
         -> Endianness
         -> MemAddr w
         -> Either (MemoryError w) (MemAddr w)
readAddr mem end addr = addrWidthClass (memAddrWidth mem) $ do
  let sz = fromIntegral (addrSize addr)
  bs <- readByteString mem addr sz
  case addrRead end bs of
    Just val -> Right $ MemAddr 0 val
    Nothing -> error $ "readAddr internal error: readByteString result too short."

-- | Read the given address as a reference to a memory segment offset, or report a
-- memory read error.
readSegmentOff :: Memory w
               -> Endianness
               -> MemAddr w
               -> Either (MemoryError w) (MemSegmentOff w)
readSegmentOff mem end addr = addrWidthClass (memAddrWidth mem) $ do
  let sz = fromIntegral (addrSize addr)
  bs <- readByteString mem addr sz
  case addrRead end bs of
    Just val -> do
      let addrInMem = MemAddr 0 val
      case asSegmentOff mem addrInMem of
        Just res -> pure res
        Nothing -> Left (InvalidAddr addrInMem)
    Nothing -> error $ "readSegmentOff internal error: readByteString result too short."

-- | Read a single byte.
readWord8 :: Memory w -> MemAddr w -> Either (MemoryError w) Word8
readWord8 mem addr = bsWord8 <$> readByteString mem addr 1

-- | Read a big endian word16
readWord16be :: Memory w -> MemAddr w -> Either (MemoryError w) Word16
readWord16be mem addr = ElfBS.bsWord16be <$> readByteString mem addr 2

-- | Read a little endian word16
readWord16le :: Memory w -> MemAddr w -> Either (MemoryError w) Word16
readWord16le mem addr = ElfBS.bsWord16le <$> readByteString mem addr 2

-- | Read a big endian word32
readWord32be :: Memory w -> MemAddr w -> Either (MemoryError w) Word32
readWord32be mem addr = ElfBS.bsWord32be <$> readByteString mem addr 4

-- | Read a little endian word32
readWord32le :: Memory w -> MemAddr w -> Either (MemoryError w) Word32
readWord32le mem addr = ElfBS.bsWord32le <$> readByteString mem addr 4

-- | Read a big endian word64
readWord64be :: Memory w -> MemAddr w -> Either (MemoryError w) Word64
readWord64be mem addr = ElfBS.bsWord64be <$> readByteString mem addr 8

-- | Read a little endian word64
readWord64le :: Memory w -> MemAddr w -> Either (MemoryError w) Word64
readWord64le mem addr = ElfBS.bsWord64le <$> readByteString mem addr 8

data NullTermString w
   = NullTermString !BS.ByteString
   | NoNullTerm
   | RelocationBeforeNull !(MemAddr w)
   | NullTermMemoryError !(MemoryError w)

-- | Attempt to read a null terminated bytesting.
readNullTermString :: MemWidth w
                  => MemSegmentOff w
                  -> NullTermString w
readNullTermString addr = do
  let seg = segoffSegment addr
  let reg = segmentBase seg
  let off = memWordValue (segmentOffset seg) + memWordValue (segoffOffset addr)
  case segoffContentsAfter addr of
    Left e -> NullTermMemoryError e
    Right [] -> NoNullTerm
    Right (ByteRegion bs:rest) -> do
      let bs' = BS.takeWhile (/= 0) bs
      if BS.length bs' == BS.length bs then
        case rest of
          [] -> NoNullTerm
          ByteRegion _:_ -> error "Misformed memory chunks"
          RelocationRegion _r:_ ->
            let off' = off + fromIntegral (BS.length bs)
                relAddr = MemAddr { addrBase = reg, addrOffset = MemWord off' }
             in RelocationBeforeNull relAddr
          BSSRegion _:_ ->
            NullTermString bs
      else
        NullTermString bs'
    Right (RelocationRegion _r:_) ->
      let relAddr = MemAddr { addrBase = reg, addrOffset = MemWord off }
       in RelocationBeforeNull relAddr
    Right (BSSRegion _:_) ->
      NullTermString BS.empty

------------------------------------------------------------------------
-- Memory finding utilities

-- | Return list of segment content memory segment ranges with its
-- content's address offset relative to segment offsets
relativeSegmentContents :: (MemWidth w) => [MemSegment w] -> [(MemAddr w, MemChunk w)]
relativeSegmentContents memSegs = concatMap relativeOffset memSegs
  where
    -- Each MemSegment has a segmentOffset indicating the offset from segmentBase its located.
    -- This makes the offsets within the MemChunk relative to that segmentOffset.
    relativeOffset :: (MemWidth w) => MemSegment w -> [(MemAddr w, MemChunk w)]
    relativeOffset seg = map (\(contentOffset,r) -> (segmentOffAddr seg contentOffset, r)) $ (contentsRanges . segmentContents) seg

-- | Naive string matching algorithm identifies matches to given
-- pattern within the list of memory segments and their corresponding
-- offset within memory. Relocations are treated as wildcards.
findByteStringMatches :: MemWidth w
                      => BS.ByteString
                      -- ^ Pattern to search for within memory segments
                      -> Integer
                      -- ^ Offset within the contents region where search is to start
                      -> [(MemAddr w, MemChunk w)]
                      -- ^ Contents of memory along with its relative
                      -- address from the segment base address.
                      -> [MemAddr w]
findByteStringMatches _ _ [] = []
findByteStringMatches pat curIndex segs@((relOffset, chunk) : rest)
  | BS.length pat == 0 = []
  | otherwise =
    if matchPrefix pat (map snd segs) then
      (currentAddr : findByteStringMatches pat nextIndex remainingElems)
    else
      findByteStringMatches pat nextIndex remainingElems
  where
    currentAddr = incAddr curIndex relOffset
    (nextIndex, remainingElems) = case chunk of
      -- drop byte in region
      ByteRegion bs ->
        if BS.length bs > 0 then
          (curIndex + 1, (relOffset, ByteRegion (BS.drop 1 bs)) : rest)
        else (0, rest)
      -- TODO: Increments within a relocation region
      _  -> (0, rest)


-- | Returns True when the given ByteString matches the bytes at the
-- beginning of this segment range and false otherwise.
matchPrefix :: MemWidth w => BS.ByteString -> [MemChunk w] -> Bool
matchPrefix _ [] = False
matchPrefix _ (BSSRegion _ : _) = False
matchPrefix pat (rel@(RelocationRegion _r) : rest)
  -- When pattern is greater than size of the relocation, skip
  -- relocation bytes in the pattern and look for match in beginning
  -- of the next range.
  | BS.length pat > (fromIntegral sz) = matchPrefix (BS.drop (fromIntegral sz) pat) rest
  -- When length of pattern is less than or equal to the size of the relocation => match
  | otherwise = True
  where sz = chunkSize rel
matchPrefix pat (ByteRegion bs : rest)
  -- Enough bytes in region to check for match directly.  This also
  -- returns true when the search pattern is empty and stops recursion
  | matchLen == prefixLen = pat == regionPrefix
    -- There aren't enough bytes in region; we need to check that
    -- the elems that do exist match the pattern prefix and
    -- that a following regions contain the remaining search pattern.
    -- NOTE: Assumes the regions are adjacent to each other.
  | otherwise = regionPrefix == (BS.take prefixLen pat) && matchPrefix (BS.drop prefixLen pat) rest
  where
    matchLen     = BS.length pat
    regionPrefix = BS.take matchLen bs
    prefixLen    = BS.length regionPrefix
