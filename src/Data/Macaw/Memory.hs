{-|
Copyright   : (c) Galois Inc, 2015-2016
Maintainer  : jhendrix@galois.com

Declares 'Memory', a type for representing segmented memory with permissions.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Memory
  ( Memory
  , memAddrWidth
  , memWidth
  , emptyMemory
  , InsertError(..)
  , showInsertError
  , insertMemSegment
  , lookupSegment
  , memSegments
  , executableSegments
  , readonlySegments
  , readAddr
  , segmentOfRange
  , addrPermissions
  , isCodeAddr
  , isCodeAddrOrNull
  , absoluteAddrSegment
  , memAsAddrPairs
    -- * AddrWidthRepr
  , AddrWidthRepr(..)
  , addrWidthNatRepr
  , addrWidthClass
    -- * Endianness
  , Endianness(..)
    -- * MemSegment operations
  , MemSegment
  , memSegment
  , SegmentIndex
  , segmentIndex
  , segmentBase
  , segmentFlags
  , segmentContents
  , ppMemSegment
  , segmentSize
  , SegmentRange(..)
  , SymbolRef(..)
  , SymbolVersion(..)
    -- * Address and offset.
  , MemWidth(..)
  , MemWord
  , memWord
  , SegmentedAddr(..)
  , addrOffset
  , addrContentsAfter
  , addrBase
  , addrValue
  , MemoryError(..)
  ) where

import           Control.Exception (assert)
import           Control.Lens
import           Data.Bits
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Foldable as Fold
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Proxy
import           Data.Word
import           GHC.TypeLits
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.NatRepr

import qualified Data.Macaw.Memory.Permissions as Perm


------------------------------------------------------------------------
-- AddrWidthRepr

-- | An address width
data AddrWidthRepr w
   = (w ~ 32) => Addr32
     -- ^ A 32-bit address
   | (w ~ 64) => Addr64
     -- ^ A 64-bit address

-- | The nat representation of this address.
addrWidthNatRepr :: AddrWidthRepr w -> NatRepr w
addrWidthNatRepr Addr32 = knownNat
addrWidthNatRepr Addr64 = knownNat

------------------------------------------------------------------------
-- Endianness

-- | Indicates whether bytes are stored in big or little endian representation.
data Endianness = BigEndian | LittleEndian

------------------------------------------------------------------------
-- Utilities

-- | Split a bytestring into an equivalent list of byte strings with a given size.
--
-- This drops the last bits if the total length is not a multiple of the size.
regularChunks :: Int -> BS.ByteString -> [BS.ByteString]
regularChunks sz bs
  | BS.length bs < sz = []
  | otherwise = BS.take sz bs : regularChunks sz (BS.drop sz bs)

bsWord32be :: BS.ByteString -> Word32
bsWord32be bs | BS.length bs /= 4 = error "bsWord32le given bytestring with bad length."
              | otherwise = w0 .|. w1 .|. w2 .|. w3
  where w0 = fromIntegral (BS.index bs 0)
        w1 = fromIntegral (BS.index bs 1) `shiftL`  8
        w2 = fromIntegral (BS.index bs 2) `shiftL` 16
        w3 = fromIntegral (BS.index bs 3) `shiftL` 24

bsWord32le :: BS.ByteString -> Word32
bsWord32le bs | BS.length bs /= 4 = error "bsWord32le given bytestring with bad length."
            | otherwise = w0 .|. w1 .|. w2 .|. w3
  where w0 = fromIntegral (BS.index bs 0)
        w1 = fromIntegral (BS.index bs 1) `shiftL`  8
        w2 = fromIntegral (BS.index bs 2) `shiftL` 16
        w3 = fromIntegral (BS.index bs 3) `shiftL` 24

bsWord64be :: BS.ByteString -> Word64
bsWord64be bs
    | BS.length bs /= 8 = error "bsWord64be given bytestring with bad length."
    | otherwise = w 0 .|. w 1 .|. w 2 .|. w 3 .|. w 4 .|. w 5 .|. w 6 .|. w 7
  where w i = fromIntegral (BS.index bs i) `shiftL` ((7 - i) `shiftL` 3)

bsWord64le :: BS.ByteString -> Word64
bsWord64le bs
    | BS.length bs /= 8 = error "bsWord64le given bytestring with bad length."
    | otherwise = w 0 .|. w 1 .|. w 2 .|. w 3 .|. w 4 .|. w 5 .|. w 6 .|. w 7
  where w i = fromIntegral (BS.index bs i) `shiftL` (i `shiftL` 3)

------------------------------------------------------------------------
-- MemBase

newtype MemWord (n :: Nat) = MemWord { memWordValue :: Word64 }
-- ^ A value in memory.

instance Show (MemWord w) where
  showsPrec _ (MemWord w) = showString "0x" . showHex w

instance Eq (MemWord w) where
  MemWord x == MemWord y = x == y

instance Ord (MemWord w) where
  compare (MemWord x) (MemWord y) = compare x y

-- | Typeclass for legal memory widths
class MemWidth w where
  -- | @addrWidthMod w@ returns @2^addrBitSize w - 1@.
  addrWidthMod :: p w -> Word64

   -- | Returns number of bytes in addr.
  addrSize :: p w -> Int

  -- Rotates the value by the given index.
  addrRotate :: MemWord w -> Int -> MemWord w

  -- | Read an address with the given endianess.
  addrRead :: Endianness -> BS.ByteString -> Maybe (MemWord w)

-- | Returns add
addrBitSize :: MemWidth w => p w -> Int
addrBitSize w = 8 * addrSize w

memWord :: forall w . MemWidth w => Word64 -> MemWord w
memWord x = MemWord (x .&. addrWidthMod p)
  where p :: Proxy w
        p = Proxy

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


instance MemWidth 32 where
  addrWidthMod _ = 0xffffffff
  addrRotate (MemWord w) i = MemWord (fromIntegral ((fromIntegral w :: Word32) `rotate` i))
  addrSize _ = 4
  addrRead e s
    | BS.length s < 4 = Nothing
    | otherwise =
      case e of
        BigEndian -> Just $ MemWord $ fromIntegral $ bsWord32be s
        LittleEndian -> Just $ MemWord $ fromIntegral $ bsWord32le s

instance MemWidth 64 where
  addrWidthMod _ = 0xffffffffffffffff
  addrRotate (MemWord w) i = MemWord (w `rotate` i)
  addrSize _ = 8
  addrRead e s
    | BS.length s < 8 = Nothing
    | otherwise =
      case e of
        BigEndian    -> Just $ MemWord $ fromIntegral $ bsWord64be s
        LittleEndian -> Just $ MemWord $ fromIntegral $ bsWord64le s

-- | Number of bytes in an address
addrWidthClass :: AddrWidthRepr w -> (MemWidth w => a) -> a
addrWidthClass Addr32 x = x
addrWidthClass Addr64 x = x

$(pure [])

-- | A unique identifier for a segment.
type SegmentIndex = Int

------------------------------------------------------------------------
-- SegmentRange

-- | Version information for a symbol
data SymbolVersion = SymbolVersion { symbolVersionFile :: !BS.ByteString
                                   , symbolVersionName :: !BS.ByteString
                                   }

-- | The name of a symbol along with optional version information.
data SymbolRef = SymbolRef { symbolName :: !BS.ByteString
                           , symbolVersion :: !(Maybe SymbolVersion)
                           }

-- | Defines a portion of a segment.
data SegmentRange w
   = ByteRegion !BS.ByteString
   | RelocatableAddr !SegmentIndex !(MemWord w)
   | SymbolicRef !SymbolRef

rangeSize :: forall w . MemWidth w => SegmentRange w -> MemWord w
rangeSize (ByteRegion bs) = fromIntegral (BS.length bs)
rangeSize (RelocatableAddr _ w) = fromIntegral (addrSize w)
rangeSize (SymbolicRef _) = fromIntegral (addrSize (error "rangeSize nat evaluated" :: NatRepr w))


instance Show (SegmentRange w) where
  showsPrec _ (ByteRegion bs) = \s -> foldr ppByte s (BS.unpack bs)
    where ppByte w | w < 16    = showChar '0' . showHex w
                   | otherwise = showHex w
  showsPrec _ (RelocatableAddr i o)  =
    showString "(seg: " . shows i . showString ", off: " . shows o . showChar ')'
  showsPrec _ (SymbolicRef s) = shows (BSC.unpack (symbolName s))

  showList [] = id
  showList (h : r) = showsPrec 10 h . showList r

------------------------------------------------------------------------
-- SegmentContents

-- | A sequence of values in the segment.
newtype SegmentContents w = SegmentContents (Map.Map (MemWord w) (SegmentRange w))

-- | Create the segment contents from a list of ranges.
contentsFromList :: MemWidth w => [SegmentRange w] -> SegmentContents w
contentsFromList elts = SegmentContents $ Map.fromList (offsets `zip` elts)
  where offsets = scanl (\s r -> s + rangeSize r) 0 elts

contentsSize :: MemWidth w => SegmentContents w -> MemWord w
contentsSize (SegmentContents m) =
  case Map.maxViewWithKey m of
    Nothing -> 0
    Just ((start, c),_) -> start + rangeSize c

-- | Read an address from the value in the segment or report a memory error.
lookupRange :: MemWidth w
            => MemWord w
            -> SegmentContents w
            -> Maybe (MemWord w, SegmentRange w)
lookupRange i (SegmentContents m) = do
  (k,r) <- Map.lookupLE i m
  Just (i-k,r)

-- | Return list of contents from given word or 'Nothing' if this can't be done
-- due to a relocation.
contentsAfter :: MemWidth w
              => MemWord w
              -> SegmentContents w
              -> Maybe [SegmentRange w]
contentsAfter off (SegmentContents m) = do
  let (premap,mv,post) = Map.splitLookup off m
  case mv of
    Just v -> Just $ v : Map.elems post
    Nothing ->
      case Map.maxViewWithKey premap of
        Nothing | off == 0 -> Just []
                | otherwise -> error $ "Memory.contentsAfter invalid contents"
        Just ((pre_off, ByteRegion bs),_) ->
          let v = ByteRegion (BS.drop (fromIntegral (off - pre_off)) bs)
           in Just $ v : Map.elems post
        Just ((_, RelocatableAddr{}),_) -> Nothing
        Just ((_, SymbolicRef{}),_) -> Nothing

contentsList :: SegmentContents w -> [(MemWord w, SegmentRange w)]
contentsList (SegmentContents m) = Map.toList m

------------------------------------------------------------------------
-- MemSegment

-- | Describes a memory segment.
--
-- Memory segments are non-overlapping regions of memory.
data MemSegment w
   = MemSegment { segmentIndex :: !SegmentIndex
                                  -- ^ Unique index for this segment
                , segmentBase  :: !(Maybe (MemWord w))
                                  -- ^ Base for this segment
                , segmentFlags :: !Perm.Flags
                                  -- ^ Permisison flags
                , segmentContents :: !(SegmentContents w)
                                     -- ^ Map from offsets to the contents of
                                     -- the segment.
                }

-- | Create a memory segment with the given values.
memSegment :: MemWidth w
           => SegmentIndex
              -- ^ Unique index of segment
           -> Maybe (MemWord w)
              -- ^ Base address if defined
           -> Perm.Flags
              -- ^ Flags if defined
           -> [SegmentRange w]
              -- ^ Range of vlaues.
           -> MemSegment w
memSegment idx base flags contents =
  MemSegment { segmentIndex = idx
             , segmentBase = base
             , segmentFlags = flags
             , segmentContents = contentsFromList contents
             }

instance Eq (MemSegment w) where
  x == y = segmentIndex x == segmentIndex y

instance Ord (MemSegment w) where
  compare x y = compare (segmentIndex x) (segmentIndex y)

-- | Return the size of the segment data.
segmentSize :: MemWidth w => MemSegment w -> MemWord w
segmentSize = contentsSize . segmentContents

-- | Pretty print a memory segment.
ppMemSegment :: MemWidth w => MemSegment w -> Doc
ppMemSegment s =
  indent 2 $ vcat [ text "index =" <+> text (show (segmentIndex s))
                  , text "base  =" <+> text (maybe "none" show (segmentBase s))
                  , text "flags =" <+> text (show (segmentFlags s))
                  , text "size  =" <+> text (show (segmentSize s))
                  ]

instance MemWidth w => Show (MemSegment w) where
  show = show . ppMemSegment

------------------------------------------------------------------------
-- SegmentedAddr

-- | A memory address is a reference to memory that uses an explicit segment plus
-- offset representation.
data SegmentedAddr w = SegmentedAddr { addrSegment :: !(MemSegment w)
                                     , _addrOffset  :: !(MemWord w)
                                     }
  deriving (Eq, Ord)

addrOffset :: Simple Lens (SegmentedAddr w) (MemWord w)
addrOffset = lens _addrOffset (\s v -> s { _addrOffset = v })

-- | Return the base value of an address or 0 if undefined.
addrBase :: MemWidth w => SegmentedAddr w -> MemWord w
addrBase addr = fromMaybe 0 (segmentBase (addrSegment addr))

-- | Return the offset of the address after adding the base segment value if defined.
addrValue :: MemWidth w => SegmentedAddr w -> MemWord w
addrValue addr = addrBase addr + addr^.addrOffset

instance Show (SegmentedAddr w) where
  showsPrec p a =
    case segmentBase (addrSegment a) of
      Just b ->
        showString "0x" . showHex (memWordValue b + memWordValue (a^.addrOffset))
      Nothing ->
        showParen (p > 6)
        $ showString "segment"
        . shows (segmentIndex (addrSegment a))
        . showString "+"
        . shows (a^.addrOffset)

-- | Return contents starting from location or throw a memory error if there
-- is an unaligned relocation.
addrContentsAfter :: MemWidth w
                  => SegmentedAddr w
                  -> Either (MemoryError w) [SegmentRange w]
addrContentsAfter addr =
  case contentsAfter (addr^.addrOffset) (segmentContents (addrSegment addr)) of
    Nothing -> Left (UnalignedRelocation addr)
    Just l  -> Right l

------------------------------------------------------------------------
-- Memory

type AbsoluteSegmentMap w = Map.Map (MemWord w) (MemSegment w)

type AllSegmentMap w = Map.Map SegmentIndex (MemSegment w)

-- | The state of the memory.
data Memory w = Memory { memAddrWidth :: !(AddrWidthRepr w)
                         -- ^ Return the address width of the memory
                       , memAbsoluteSegments :: !(AbsoluteSegmentMap w)
                       , memAllSegments      :: !(AllSegmentMap w)
                       }

-- | Return nat repr associated with memory.
memWidth :: Memory w -> NatRepr w
memWidth = addrWidthNatRepr . memAddrWidth

instance MemWidth w => Show (Memory w) where
  show m = show (Fold.toList (memAllSegments m))

-- | A memory with no segments.
emptyMemory :: AddrWidthRepr w -> Memory w
emptyMemory w = Memory { memAddrWidth        = w
                       , memAbsoluteSegments = Map.empty
                       , memAllSegments      = Map.empty
                       }

-- | Get memory segments.
memSegments :: Memory w -> [MemSegment w]
memSegments m = Map.elems (memAllSegments m)

-- | Return segment with given index in memory.
lookupSegment :: Memory w -> SegmentIndex -> Maybe (MemSegment w)
lookupSegment m i = Map.lookup i (memAllSegments m)

-- | Return list of segmented address values in memory.
--
-- Each address includes the value and the base.
memAsAddrPairs :: MemWidth w
               => Memory w
               -> Endianness
               -> [(SegmentedAddr w, SegmentedAddr w)]
memAsAddrPairs mem end = do
  seg <- memSegments mem
  (contents_offset,r) <- contentsList (segmentContents seg)
  let addr = SegmentedAddr seg contents_offset
  let sz = addrSize mem
  case r of
    ByteRegion bs -> assert (BS.length bs `rem` fromIntegral sz == 0) $ do
      w <- regularChunks (fromIntegral sz) bs
      let Just val = addrRead end w
      case Map.lookupLE val (memAbsoluteSegments mem) of
        Just (base, value_seg) | val <= base + segmentSize value_seg -> do
          let seg_val =  SegmentedAddr value_seg (val - base)
           in [(addr,seg_val)]
        _ -> []
    RelocatableAddr idx value_offset ->
      case lookupSegment mem idx of
        Just value_seg -> [(addr, SegmentedAddr value_seg value_offset)]
        Nothing -> error "memAsAddrPairs found segment without valid index."
    SymbolicRef{} -> []

-- | Get executable segments.
executableSegments :: Memory w -> [MemSegment w]
executableSegments = filter (Perm.isExecutable . segmentFlags) . memSegments

readonlySegments :: Memory w -> [MemSegment w]
readonlySegments = filter (Perm.isReadonly . segmentFlags) . memSegments

-- | Given an absolute address, this returns a segment and offset into the segment.
absoluteAddrSegment :: MemWidth w => Memory w -> MemWord w -> Maybe (SegmentedAddr w)
absoluteAddrSegment mem addr =
  case Map.lookupLE addr (memAbsoluteSegments mem) of
    Just (base, seg) | addr < base + segmentSize seg ->
      Just $! SegmentedAddr { addrSegment = seg
                            , _addrOffset = addr - base
                            }
    _ -> Nothing

-- | Read an address from the value in the segment or report a memory error.
readAddr :: MemWidth w
         => Memory w
         -> Endianness
         -> SegmentedAddr w
         -> Either (MemoryError w) (SegmentedAddr w)
readAddr mem end addr = do
  let sz = fromIntegral (addrSize addr)
  case lookupRange (addr^.addrOffset) (segmentContents (addrSegment addr)) of
    Just (MemWord offset, ByteRegion bs)
      | offset + sz >= offset                           -- Check for no overfow
      , offset + sz < fromIntegral (BS.length bs) -> do -- Check length
        let Just val = addrRead end (BS.take (fromIntegral sz) (BS.drop (fromIntegral offset) bs))
        case Map.lookupLE val (memAbsoluteSegments mem) of
          Just (base, seg) | val <= base + segmentSize seg -> Right $
            SegmentedAddr { addrSegment = seg
                          , _addrOffset = val - base
                          }
          _ -> Left (InvalidAddr addr)

    -- We encountered a relocat
    Just (MemWord offset, RelocatableAddr idx a)
      | offset == 0 ->
          case lookupSegment mem idx of
             Just seg -> Right (SegmentedAddr seg a)
             Nothing -> error $ "Read address given invalid segment index."

      | otherwise ->
        Left (UnalignedRelocation addr)

    _ | otherwise ->
        Left (AccessViolation addr)

data InsertError w
   = OverlapSegment (MemWord w) (MemSegment w)
     -- ^ The inserted segment overlaps with the given segment.
   | IndexAlreadyUsed (MemSegment w)
     -- ^ The segment index has already been added to this memory object.

showInsertError :: InsertError w -> String
showInsertError (OverlapSegment _base _seg) =
  "overlaps with memory segment."
showInsertError (IndexAlreadyUsed seg) =
  "has the same index as another segment (" ++ show (segmentIndex seg) ++ ")."


insertAbsoluteSegmentMap :: MemWidth w
                         => MemSegment w
                         -> AbsoluteSegmentMap w
                         -> Either (InsertError w) (AbsoluteSegmentMap w)
insertAbsoluteSegmentMap seg m =
  case segmentBase seg of
    Nothing -> Right m
    Just base ->
      case Map.lookupGE base m of
        Just (next,old) | next < base + segmentSize seg ->
          Left (OverlapSegment base old)
        _ ->
          Right (Map.insert base seg m)

insertAllSegmentMap :: MemSegment w
                    -> AllSegmentMap w
                    -> Either (InsertError w) (AllSegmentMap w)
insertAllSegmentMap seg m =
  case Map.lookup (segmentIndex seg) m of
    Nothing ->
      Right (Map.insert (segmentIndex seg) seg m)
    Just old ->
      Left (IndexAlreadyUsed old)

-- | Insert segment into memory or fail if this overlaps with another
-- segment in memory.
insertMemSegment :: MemWidth w
                 => MemSegment w
                 -> Memory w
                 -> Either (InsertError w) (Memory w)
insertMemSegment seg mem = do
  absMap <- insertAbsoluteSegmentMap seg (memAbsoluteSegments mem)
  allMap <- insertAllSegmentMap      seg (memAllSegments mem)
  pure $ mem { memAbsoluteSegments = absMap
             , memAllSegments      = allMap
             }

-- | Return segment if range is entirely contained within a single segment
-- and 'Nothing' otherwise.
segmentOfRange :: MemWidth w
               => MemWord w -- ^ Start of range
               -> MemWord w -- ^ One past last index in range.
               -> Memory w
               -> Maybe (MemSegment w)
segmentOfRange base end mem =
  case Map.lookupLE base (memAbsoluteSegments mem) of
    Just (seg_base, seg) | end <= seg_base + segmentSize seg -> Just seg
    _ -> Nothing

-- | Return true if address satisfies permissions check.
addrPermissions :: MemWidth w => MemWord w -> Memory w -> Perm.Flags
addrPermissions addr mem =
  case Map.lookupLE addr (memAbsoluteSegments mem) of
    Just (base, seg) | addr < base + segmentSize seg -> segmentFlags seg
    _ -> Perm.none

-- | Indicates if address is a code pointer.
isCodeAddr :: MemWidth w => Memory w -> MemWord w -> Bool
isCodeAddr mem val = addrPermissions val mem `Perm.hasPerm` Perm.execute

-- | Indicates if address is an address in code segment or null.
isCodeAddrOrNull :: MemWidth w => Memory w -> MemWord w -> Bool
isCodeAddrOrNull _ (MemWord 0) = True
isCodeAddrOrNull mem a = isCodeAddr mem a

------------------------------------------------------------------------
-- MemoryError

-- | Type of errors that may occur when reading memory.
data MemoryError w
   = UserMemoryError (SegmentedAddr w) !String
     -- ^ the memory reader threw an unspecified error at the given location.
   | InvalidInstruction (SegmentedAddr w) ![SegmentRange w]
     -- ^ The memory reader could not parse the value starting at the given address.
   | AccessViolation (SegmentedAddr w)
     -- ^ Memory could not be read, because it was not defined.
   | PermissionsError (SegmentedAddr w)
     -- ^ Memory could not be read due to insufficient permissions.
   | UnalignedRelocation (SegmentedAddr w)
     -- ^ Read from location that partially overlaps a relocated entry
   | InvalidAddr (SegmentedAddr w)
     -- ^ The data at the given address did not refer to a valid memory location.

instance Show (MemoryError w) where
  show (UserMemoryError _ msg) = msg
  show (InvalidInstruction start contents) =
    "Invalid instruction at " ++ show start ++ ": " ++ showList contents ""
  show (AccessViolation a)   =
    "Access violation at " ++ show a ++ "."
  show (PermissionsError a)  =
    "Insufficient permissions at " ++ show a ++ "."
  show (UnalignedRelocation a)   =
    "Attempt to read an offset of a relocation entry at " ++ show a ++ "."
  show (InvalidAddr a)   =
    "Attempt to interpret an invalid address: " ++ show a ++ "."
