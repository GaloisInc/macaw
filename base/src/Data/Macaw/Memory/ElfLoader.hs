{-|
Copyright   : Galois Inc, 2016-18
Maintainer  : jhendrix@galois.com

Operations for creating a view of memory from an elf file.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.Memory.ElfLoader
  ( memoryForElf
  , memoryForElf'
  , memoryForElfAllSymbols
  , memoryForElfSections
  , memoryForElfSegments
  , memoryForElfSegments'
  , SectionIndexMap
  , MemLoadWarning(..)
  , RelocationError
  , SectionName
  , resolveElfContents
  , elfAddrWidth
  , adjustedLoadRegionIndex
    -- * Symbols
  , MemSymbol(..)
  , SymbolResolutionError(..)
  , SymbolTable(..)
    -- * Re-exports
  , module Data.Macaw.Memory.LoadCommon
  , module Data.Macaw.Memory
  , module Data.Macaw.Memory.Symbols
  ) where

import           Control.Lens
import           Control.Monad (when)
import           Control.Monad.Except (Except, ExceptT, MonadError(..), runExcept, runExceptT)
import           Control.Monad.State.Strict (State, StateT(..), execStateT, gets, modify, runState)
import           Data.Bits
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.ElfEdit.Prim
  ( ElfWordType
  , ElfClass(..)

  , ElfSectionIndex(..)
  , ElfSectionFlags
  , ElfSegmentFlags
  )
import qualified Data.ElfEdit.Prim as Elf
import           Data.Foldable
import           Data.IntervalMap.Strict (Interval(..), IntervalMap)
import qualified Data.IntervalMap.Strict as IMap
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import           Data.Word
import           Numeric (showHex)

import           Data.Macaw.Memory
import           Data.Macaw.Memory.LoadCommon
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Memory.Symbols

-- | Return a subrange of a bytestring.
slice :: Integral w => Elf.FileRange w -> BS.ByteString -> BS.ByteString
slice (i,c) = BS.take (fromIntegral c) . BS.drop (fromIntegral i)

-- | Return the addr width repr associated with an elf class
elfAddrWidth :: ElfClass w -> AddrWidthRepr w
elfAddrWidth ELFCLASS32 = Addr32
elfAddrWidth ELFCLASS64 = Addr64

------------------------------------------------------------------------
-- SectionIndexMap

-- | Maps section indices that are loaded in memory to their associated base
-- address and section contents.
--
-- The base address is expressed in terms of the underlying memory segment.
type SectionIndexMap w = Map Word16 (MemSegmentOff w)

------------------------------------------------------------------------
-- Flag conversion

-- | Create Reopt flags from elf flags.
flagsForSegmentFlags :: ElfSegmentFlags -> Perm.Flags
flagsForSegmentFlags f
    =   flagIf Elf.pf_r Perm.read
    .|. flagIf Elf.pf_w Perm.write
    .|. flagIf Elf.pf_x Perm.execute
  where flagIf :: ElfSegmentFlags -> Perm.Flags -> Perm.Flags
        flagIf ef pf | f `Elf.hasPermissions` ef = pf
                     | otherwise = Perm.none

-- | Convert elf section flags to a segment flags.
flagsForSectionFlags :: forall w
                     .  (Num w, Bits w)
                     => ElfSectionFlags w
                     -> Perm.Flags
flagsForSectionFlags f =
    Perm.read .|. flagIf Elf.shf_write Perm.write .|. flagIf Elf.shf_execinstr Perm.execute
  where flagIf :: ElfSectionFlags w -> Perm.Flags -> Perm.Flags
        flagIf ef pf = if f `Elf.hasPermissions` ef then pf else Perm.none

------------------------------------------------------------------------
-- RelocationError

data RelocationError
   = MissingSymbolTable
     -- ^ The file is missing a symbol table.
   | RelocationZeroSymbol
     -- ^ A relocation refers to the symbol index 0.
   | RelocationBadSymbolIndex !Int
     -- ^ A relocation entry referenced a bad symbol index.
   | RelocationUnsupportedType !String
     -- ^ We do not support this type of relocation.
   | RelocationFileUnsupported
     -- ^ We do not allow relocations to refer to the "file" as in Elf.
   | RelocationInvalidAddend !String !Integer !SymbolIdentifier
     -- ^ The relocation type given does not allow the adddend with the given value.
   | RelocationEvenAddend !String !Integer !BSC.ByteString !Integer
     -- ^ The relocation type must have an even addend.
   | RelocationDynamicError Elf.DynamicError
     -- ^ Parsing the dynamic section failed when resolving a symbol.

instance Show RelocationError where
  show MissingSymbolTable =
    "Relocations cannot be applied due to missing symbol table."
  show RelocationZeroSymbol =
    "A relocation entry referred to invalid 0 symbol index."
  show (RelocationBadSymbolIndex idx) =
    "A relocation entry referred to invalid symbol index " ++ show idx ++ "."
  show (RelocationUnsupportedType tp) =
    "Unsupported relocation type " ++ tp
  show RelocationFileUnsupported =
    "Do not support relocations referring to file entry."
  show (RelocationEvenAddend tp addr sym addend) =
    let tgt = show sym ++ " + " ++ show addend
     in "The " ++ tp ++ " relocation applied to " ++ show addr
        ++ " with target " ++ tgt ++ " must have an even addend."
  show (RelocationInvalidAddend tp v sym) =
    "Do not support addend of " ++ show v ++ " with relocation type " ++ tp ++ " to " ++ show sym ++ "."
  show (RelocationDynamicError e) = show e

------------------------------------------------------------------------
-- MemLoader

type SectionName = BS.ByteString

data MemLoadWarning
  = SectionNotAlloc !SectionName
  | MultipleSectionsWithName !SectionName
  | MultipleDynamicSegments
  | OverlappingLoadableSegments
  | UnsupportedSection !SectionName
  | UnknownDefinedSymbolBinding   !SymbolName Elf.ElfSymbolBinding
  | UnknownDefinedSymbolType      !SymbolName Elf.ElfSymbolType
  | UnknownUndefinedSymbolBinding !SymbolName Elf.ElfSymbolBinding
  | UnknownUndefinedSymbolType    !SymbolName Elf.ElfSymbolType
  | ExpectedSectionSymbolNameEmpty !SymbolName
  | ExpectedSectionSymbolLocal
  | InvalidSectionSymbolIndex !Elf.ElfSectionIndex
  | UnsupportedProcessorSpecificSymbolIndex !SymbolName !ElfSectionIndex

  | MultipleRelocationTables
    -- ^ Issued if the file contains multiple relocation tables.
  | RelocationParseFailure !String
  | DynamicTagsOutOfRange !Elf.ElfDynamicTag !Elf.ElfDynamicTag !Word64 !Word64
    -- ^ The range referenced by the dynamic tags was  range.
  | DynamicTagPairMismatch !Elf.ElfDynamicTag !Elf.ElfDynamicTag
    -- ^ We expected either both tags or neither.
  | DynamicMultipleTags !Elf.ElfDynamicTag
    -- ^ We expected at most a single value of the given tag, but failed multiple.
  | AndroidRelWithNonzeroAddend
    -- ^ The `DT_ANDROID_REL` section contains Android relocations with non-zero addends.
  | AndroidRelDecodingError !Elf.ElfDynamicTag !Elf.AndroidDecodeError
    -- ^ We could not decode the table identified by the given dynamic tag.
  | MultipleRelocationsAtAddr !Word64
    -- ^ Multiple relocations at the given offset
  | IgnoreRelocation !RelocationError
    -- ^ @IgnoreRelocation err@ warns we ignored a relocation.

ppSymbol :: SymbolName -> String
ppSymbol "" = "unnamed symbol"
ppSymbol nm = "symbol " ++ BSC.unpack nm

instance Show MemLoadWarning where
  show (SectionNotAlloc nm) =
    "Section " ++ BSC.unpack nm ++ " was not marked as allocated."
  show (MultipleSectionsWithName nm) =
    "Found multiple sections named " ++ BSC.unpack nm ++ "; arbitrarily choosing first one encountered."
  show MultipleDynamicSegments =
    "Found multiple dynamic segments; choosing first one."
  show OverlappingLoadableSegments =
    "File segments containing overlapping addresses; skipping relocations."
  show (UnsupportedSection nm) =
    "Do not support section " ++ BSC.unpack nm
  show (UnknownDefinedSymbolBinding nm bnd) =
    "Unsupported binding " ++ show bnd ++ " for defined " ++ ppSymbol nm
    ++ "; Treating as a strong symbol."
  show (UnknownDefinedSymbolType nm tp) =
    "Unsupported type " ++ show tp ++ " for defined " ++ ppSymbol nm
    ++ "; Treating as a strong symbol."
  show (UnknownUndefinedSymbolBinding nm bnd) =
    "Unsupported binding " ++ show bnd ++ " for undefined " ++ ppSymbol nm
    ++ "; Treating as a required symbol."
  show (UnknownUndefinedSymbolType nm tp) =
    "Unsupported type " ++ show tp ++ " for undefined " ++ ppSymbol nm
    ++ "; Treating as a strong symbol."
  show (ExpectedSectionSymbolNameEmpty nm) =
    "Expected section symbol to have empty name instead of " ++ ppSymbol nm ++ "."
  show ExpectedSectionSymbolLocal =
    "Expected section symbol to have local visibility."
  show (InvalidSectionSymbolIndex idx) =
    "Expected section symbol to have a valid index instead of " ++ show idx ++ "."
  show (UnsupportedProcessorSpecificSymbolIndex nm idx) =
    "Could not resolve symbol index " ++ show idx ++ " for symbol " ++ BSC.unpack nm ++ "."
  show MultipleRelocationTables =
    "File contains multiple relocation tables; these are being merged."
  show (RelocationParseFailure msg) =
    "Error parsing relocations: " ++ msg
  show (DynamicTagsOutOfRange offTag szTag off sz) =
    show offTag ++ " and " ++ show szTag ++ " referenced a range [" ++ show (toInteger off)
    ++ " to " ++ show (toInteger off + toInteger sz) ++ "that is outside the file bounds."
  show (DynamicTagPairMismatch foundTag notfoundTag) =
    "Found " ++ show foundTag ++ " but missing " ++ show notfoundTag ++ "."
  show (DynamicMultipleTags tag) =
    "Multiple values assigned to " ++ show tag ++ " in dynamic information."
  show AndroidRelWithNonzeroAddend =
    "The DT_ANDROID_REL region in the dynamic is ignoring relocations with non-zero addends."
  show (AndroidRelDecodingError tag nm) =
    "The " ++ show tag ++ " region generated decoding error: " ++ show nm
  show (MultipleRelocationsAtAddr addr) =
    "Multiple relocations modify " ++ showHex addr "."
  show (IgnoreRelocation err) =
    show err

data MemLoaderState w = MLS { _mlsMemory :: !(Memory w)
                            , mlsEndianness :: !Endianness
                              -- ^ Endianness of elf file
                            , _mlsIndexMap :: !(SectionIndexMap w)
                            , mlsWarnings :: ![MemLoadWarning]
                            }

mlsMemory :: Simple Lens (MemLoaderState w) (Memory w)
mlsMemory = lens _mlsMemory (\s v -> s { _mlsMemory = v })

-- | Map from elf section indices to their offset and section
mlsIndexMap :: Simple Lens (MemLoaderState w) (SectionIndexMap w)
mlsIndexMap = lens _mlsIndexMap (\s v -> s { _mlsIndexMap = v })

addWarning :: MemLoadWarning -> MemLoader w ()
addWarning w = modify $ \s -> s { mlsWarnings = w : mlsWarnings s }

type MemLoader w = StateT (MemLoaderState w) (Except (LoadError w))

-- || Error occured from loading
data LoadError w
   = LoadInsertError !String !(InsertError w)
     -- ^ Error occurred in inserting a segment into memory.
   | UnsupportedArchitecture !String
     -- ^ Do not support relocations on given architecture.
   | FormatDynamicError !Elf.DynamicError
     -- ^ An error occured in parsing the dynamic segment.

instance MemWidth w => Show (LoadError w) where
  show (LoadInsertError nm (OverlapSegment _ old)) =
    nm ++ " overlaps with memory segment: " ++ show (segmentOffset old)
  show (UnsupportedArchitecture arch) =
    "Dynamic libraries are not supported on " ++ arch ++ "."
  show (FormatDynamicError e) =
    "Elf parsing error: " ++ show e

-- | This contains information needed to resolve elf symbol addresses.
data SymbolAddrResolver w =
  SymbolAddrResolver { symSecCount :: Word16
                     , symResolver :: Word16 -> ElfWordType w -> Maybe (MemSegmentOff w)
                       -- ^ Given a section index and offset, this returns the memory addr
                       -- or nothing if that cannot be determined.
                     }

mkSymbolAddrResolver :: (MemWidth w, Integral (ElfWordType w))
                     => V.Vector (Elf.Shdr Word32 (Elf.ElfWordType w))
                     -> SectionIndexMap w
                     -> SymbolAddrResolver w
mkSymbolAddrResolver v m = do
  let resolveFn secIdx val = do
        case Map.lookup secIdx m of
          Just base
            | Just s <- v V.!? fromIntegral secIdx
            , Elf.shdrAddr s <= val && (val - Elf.shdrAddr s) < Elf.shdrSize s
            , off <- toInteger (val - Elf.shdrAddr s) ->
              incSegmentOff base off
          _ -> Nothing
   in SymbolAddrResolver { symSecCount = fromIntegral (V.length v)
                         , symResolver = resolveFn
                         }

runMemLoader :: Endianness
             -> Memory  w
             -> MemLoader w ()
             -> Either String (Memory w, SectionIndexMap w, [MemLoadWarning])
runMemLoader end mem m =
   let s = MLS { _mlsMemory = mem
               , _mlsIndexMap = Map.empty
               , mlsWarnings = []
               , mlsEndianness = end
               }
    in case runExcept $ execStateT m s of
         Left e -> Left $ addrWidthClass (memAddrWidth mem) (show e)
         Right mls -> do
           Right (mls^.mlsMemory, mls^.mlsIndexMap, reverse (mlsWarnings mls))

-- | This adds a Macaw mem segment to the memory
loadMemSegment :: MemWidth w => String -> MemSegment w -> MemLoader w ()
loadMemSegment nm seg =
  StateT $ \mls ->
    case insertMemSegment seg (mls^.mlsMemory) of
      Left e ->
        throwError $ LoadInsertError nm e
      Right mem' ->
        pure ((), mls & mlsMemory .~ mem')

-- | Maps file offsets to the elf section
type ElfFileSectionMap v = IntervalMap v Word16

------------------------------------------------------------------------
-- SymbolResolver

type SymbolResolver a = ExceptT RelocationError (State [MemLoadWarning]) a

runSymbolResolver :: SymbolResolver a -> MemLoader w (Either RelocationError a)
runSymbolResolver m = do
  warn <- gets mlsWarnings
  let (er, warn') = runState (runExceptT m) warn
  modify $ \s -> s { mlsWarnings = warn' }
  pure er

symbolWarning :: MemLoadWarning -> SymbolResolver ()
symbolWarning w = modify $ \l -> w:l

------------------------------------------------------------------------
-- SymbolTable

-- | This wraps a callback function that lets users lookup symbol information by index
-- from the Elf file.
--
-- It is implemented using a callback function as the Elf dynamic
-- section doesn't provide an explicit number of symbol table
-- elements, and we decided not to depend on meta data such as section
-- names that could be stripped from executables/shared objects.
data SymbolTable w
   = NoSymbolTable
   | StaticSymbolTable !(V.Vector (Elf.SymtabEntry BS.ByteString (Elf.ElfWordType w)))
   | DynamicSymbolTable !(Elf.DynamicSection w) !(Elf.VirtAddrMap w) !Elf.VersionDefMap !Elf.VersionReqMap

-- | Take a symbol entry and symbol version and return the identifier.
resolveSymbolId :: Elf.SymtabEntry BS.ByteString wtp
                -> SymbolVersion
                -> SymbolResolver SymbolIdentifier
resolveSymbolId sym ver = do
  let nm = Elf.steName sym
  let idx = Elf.steIndex sym
  case Elf.steType sym of
    Elf.STT_SECTION
      | idx < Elf.SHN_LOPROC -> do
          when (nm /= "") $
            symbolWarning $ ExpectedSectionSymbolNameEmpty nm
          when (Elf.steBind sym /= Elf.STB_LOCAL) $
            symbolWarning ExpectedSectionSymbolLocal
          pure $ SectionIdentifier (Elf.fromElfSectionIndex idx)
      | otherwise -> do
          symbolWarning $ InvalidSectionSymbolIndex idx
          pure $ SymbolRelocation nm ver
    Elf.STT_FILE -> do
      throwError RelocationFileUnsupported
    _tp -> do
      when (idx >= Elf.SHN_LOPROC && idx `notElem` [Elf.SHN_ABS, Elf.SHN_COMMON]) $ do
        symbolWarning $ UnsupportedProcessorSpecificSymbolIndex nm idx
      pure $ SymbolRelocation nm ver

resolveSymbol :: SymbolTable w
              -> Word32
              -> SymbolResolver
                  ( Elf.SymtabEntry BS.ByteString (Elf.ElfWordType w)
                  , SymbolVersion
                  )
resolveSymbol NoSymbolTable _symIdx =
  throwError MissingSymbolTable
resolveSymbol (StaticSymbolTable entries) symIdx = do
  when (symIdx == 0) $
    throwError RelocationZeroSymbol
  case entries V.!? fromIntegral symIdx of
    Nothing ->
      throwError $ RelocationBadSymbolIndex $ fromIntegral symIdx
    Just sym ->
      -- Look for '@' as it is used to separate symbol name from version information
      -- in object files.
      case BSC.findIndex (== '@') (Elf.steName sym) of
        Just i -> do
          let nm = Elf.steName sym
                  -- If "@@" appears in the symbol, this is a default versioned symbol
          let ver | i+1 < BSC.length nm, BSC.index nm (i+1) == '@' =
                      ObjectDefaultSymbol (BSC.drop (i+2) nm)
                  -- Otherwise "@" appears in the symbol, and this is a non-default symbol.
                  | otherwise =
                      ObjectNonDefaultSymbol (BSC.drop (i+1) nm)
          pure (sym { Elf.steName = BSC.take i nm }, ver)
        Nothing -> do
          pure (sym, UnversionedSymbol)
resolveSymbol (DynamicSymbolTable ds virtMap verDefMap verReqMap) symIdx = do
  when (symIdx == 0) $
    throwError RelocationZeroSymbol
  case Elf.dynSymEntry ds virtMap verDefMap verReqMap symIdx of
    Left e -> throwError (RelocationDynamicError e)
    Right (sym, mverId) -> do
      let ver = case mverId of
                  Elf.VersionLocal -> UnversionedSymbol
                  Elf.VersionGlobal -> UnversionedSymbol
                  Elf.VersionSpecific elfVer -> VersionedSymbol (Elf.verFile elfVer) (Elf.verName elfVer)
      pure (sym, ver)

------------------------------------------------------------------------
-- Relocations

data RelFlag = IsRel | IsRela
  deriving (Eq, Ord, Show)

-- | A function that resolves the architecture-specific relocation-type
-- into a symbol reference.  The input
type RelocationResolver tp
  =  Maybe SegmentIndex
     -- ^ Index of segment in which this relocation will be applied if this is
     -- a dynamic relocation, and `Nothing` otherwise.
  -> SymbolTable (Elf.RelocationWidth tp)
  -> Elf.RelEntry tp
     -- ^ Relocation information
  -> MemWord (Elf.RelocationWidth tp)
     -- ^ Addend to add to symbol.
  -> RelFlag
     -- ^ Flag to indicate if this is a rela and rel relocation
     --
     -- Added because some relocations (i.e. PLT ones) will ignore
     -- Rel relocation addends.
  -> SymbolResolver (Relocation (Elf.RelocationWidth tp))

data SomeRelocationResolver w
  = forall tp
  . (Elf.IsRelocationType tp, w ~ Elf.RelocationWidth tp)
  => SomeRelocationResolver (RelocationResolver tp)

-- T is 1 if the target symbol S has type STT_FUNC and the symbol addresses a Thumb instruction; it is 0 otherwise.


-- | This attempts to resolve an index in the symbol table to the
-- identifier information needed to resolve its loaded address.
resolveRelocationSym :: SymbolTable w
                      -- ^ A vector mapping symbol indices to the
                      -- associated symbol information.
                      -> Word32
                      -- ^ Index in the symbol table this refers to.
                      -> SymbolResolver SymbolIdentifier
resolveRelocationSym symtab symIdx = do
  (symEntry, ver) <- resolveSymbol symtab symIdx
  resolveSymbolId symEntry ver


-- | Attempt to resolve an X86_64 specific symbol.
relaTargetX86_64 :: Maybe SegmentIndex
                 -> SymbolTable 64
                 -- ^ Symbol table to look up symbols in/
                 -> Elf.RelEntry Elf.X86_64_RelocationType
                 -> MemWord 64
                 -- ^ Addend to add to symbol.
                 -> RelFlag
                 -> SymbolResolver (Relocation 64)
relaTargetX86_64 _ symtab rel addend _isRel =
  case Elf.relType rel of
    Elf.R_X86_64_64 -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $ Relocation { relocationSym        = sym
                        , relocationOffset     = addend
                        , relocationIsRel      = False
                        , relocationSize       = 8
                        , relocationIsSigned   = False
                        , relocationEndianness = LittleEndian
                        , relocationJumpSlot   = False
                        }
    Elf.R_X86_64_PC32 -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $ Relocation { relocationSym        = sym
                        , relocationOffset     = addend
                        , relocationIsRel      = True
                        , relocationSize       = 4
                        , relocationIsSigned   = False
                        , relocationEndianness = LittleEndian
                        , relocationJumpSlot   = False
                        }
    -- This is used for constructing relative jumps from a caller to the
    -- PLT stub for the function it is calling.  Such jumps typically modify
    -- a relative call instruction with four bytes for the distance, and so
    -- the distance must be an unsigned 4-byte value.
    Elf.R_X86_64_PLT32 -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $ Relocation { relocationSym    = sym
                        , relocationOffset = addend
                        , relocationIsRel  = True
                        , relocationSize   = 4
                        , relocationIsSigned   = False
                        , relocationEndianness = LittleEndian
                        , relocationJumpSlot   = True
                        }
    -- R_X86_64_GLOB_DAT are used to update GOT entries with their
    -- target address.  They are similar to R_x86_64_64 except appear
    -- inside dynamically linked executables/libraries, and are often
    -- loaded lazily.  We just use the eager AbsoluteRelocation here.
    Elf.R_X86_64_GLOB_DAT -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $ Relocation { relocationSym        = sym
                        , relocationOffset     = addend
                        , relocationIsRel      = False
                        , relocationSize       = 8
                        , relocationIsSigned   = False
                        , relocationEndianness = LittleEndian
                        , relocationJumpSlot   = False
                        }
    Elf.R_X86_64_JUMP_SLOT -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $ Relocation { relocationSym = sym
                        , relocationOffset = addend
                        , relocationIsRel = False
                        , relocationSize  = 8
                        , relocationIsSigned = False
                        , relocationEndianness = LittleEndian
                        , relocationJumpSlot = True
                        }
    Elf.R_X86_64_RELATIVE -> do
      when (Elf.relSym rel /= 0) $ do
        throwError $ RelocationBadSymbolIndex (fromIntegral (Elf.relSym rel))
      pure $ Relocation { relocationSym        = LoadBaseAddr
                        , relocationOffset     = addend
                        , relocationIsRel      = False
                        , relocationSize       = 8
                        , relocationIsSigned   = False
                        , relocationEndianness = LittleEndian
                        , relocationJumpSlot   = False
                        }
    Elf.R_X86_64_32 -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $ Relocation { relocationSym        = sym
                        , relocationOffset     = addend
                        , relocationIsRel      = False
                        , relocationSize       = 4
                        , relocationIsSigned   = False
                        , relocationEndianness = LittleEndian
                        , relocationJumpSlot   = False
                        }
    Elf.R_X86_64_32S -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $ Relocation { relocationSym        = sym
                        , relocationOffset     = addend
                        , relocationIsRel      = False
                        , relocationSize       = 4
                        , relocationIsSigned   = True
                        , relocationEndianness = LittleEndian
                        , relocationJumpSlot   = False
                        }
    Elf.R_X86_64_COPY -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      when (addend /= 0) $ do
        throwError $ RelocationUnsupportedType (show (Elf.relType rel))
      pure $ Relocation { relocationSym        = sym
                        , relocationOffset     = 0
                        , relocationIsRel      = False
                        , relocationSize       = 8
                        , relocationIsSigned   = False
                        , relocationEndianness = LittleEndian
                        , relocationJumpSlot   = False
                        }
    -- Jhx Note. These will be needed to support thread local variables.
    --   Elf.R_X86_64_TPOFF32 -> undefined
    --   Elf.R_X86_64_GOTTPOFF -> undefined

    tp -> throwError $ RelocationUnsupportedType (show tp)

-- | Generate an absolute 32-bit relocation.
relocARM32Abs :: Endianness
              -> SymbolTable 32 -- ^ Symbol table
              -> Elf.RelEntry Elf.ARM32_RelocationType -- ^ Relocation entry
              -> MemWord 32
              -> SymbolResolver (Relocation 32)
relocARM32Abs end symtab rel addend = do
  (symEntry, ver) <- resolveSymbol symtab (Elf.relSym rel)
  sym <- resolveSymbolId symEntry ver
  -- These relocation relocations can apply to code or data, but we
  -- want to ensure relocations do not change the thumb bit
  -- of the symbol.
  when (Elf.steType symEntry == Elf.STT_FUNC && addend `testBit` 0) $ do
    let tp = show (Elf.relType rel)
    let addr = toInteger (Elf.relAddr rel)
    throwError $
      RelocationEvenAddend tp addr (Elf.steName symEntry) (toInteger addend)
  pure $! Relocation { relocationSym        = sym
                     , relocationOffset     = addend
                     , relocationIsRel      = False
                     , relocationSize       = 4
                     , relocationIsSigned   = False
                     , relocationEndianness = end
                     , relocationJumpSlot   = False
                     }

-- | Attempt to resolve an X86_64 specific symbol.
relaTargetARM32 :: Endianness
                 -- ^ Endianness of relocations
                -> Maybe SegmentIndex
                -- ^ Index of segment for dynamic relocations
                -> SymbolTable 32 -- ^ Symbol table
                -> Elf.RelEntry Elf.ARM32_RelocationType -- ^ Relocation entry
                -> MemWord 32
                -- ^ Addend of symbol
                -> RelFlag
                -> SymbolResolver (Relocation 32)
relaTargetARM32 end msegIndex symtab rel addend relFlag =
  case Elf.relType rel of
    -- A static 32-bit absolute relocation
    Elf.R_ARM_ABS32 -> do
      relocARM32Abs end symtab rel addend
    -- A dynamic 32-bit absolute relocation that typically applies to data.
    Elf.R_ARM_GLOB_DAT -> do
      relocARM32Abs end symtab rel addend
    Elf.R_ARM_RELATIVE -> do
      -- This relocation has the value B(S) + A where
      -- - A is the addend for the relocation, and
      -- - B(S) with S ≠ 0 resolves to the difference between the
      --   address at which the segment defining the symbol S was
      --   loaded and the address at which it was linked.
      --  - B(S) with S = 0 resolves to the difference between the
      --    address at which the segment being relocated was loaded
      --    and the address at which it was linked.
      --
      -- Since the address at which it was linked is a constant, we
      -- create a non-relative address but subtract the link address
      -- from the offset.

      -- Get the address at which it was linked so we can subtract from offset.
      let linktimeAddr = Elf.relAddr rel

      -- Resolve the symbol using the index in the relocation.
      sym <-
        if Elf.relSym rel == 0 then do
          case msegIndex of
            Nothing -> do
              throwError $ RelocationZeroSymbol
            Just idx ->
              pure $! SegmentBaseAddr idx
        else do
          resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend - fromIntegral linktimeAddr
                         , relocationIsRel      = False
                         , relocationSize       = 4
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
    Elf.R_ARM_JUMP_SLOT -> do
      -- This is a PLT relocation
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      -- For rela entries, check that addend is 0
      -- N.B. Rel entries read from the target bits, and these typically point to the
      -- start of the PLT, but are otherwise ignored for relocation purposes.
      when (relFlag == IsRela && addend /= 0) $ do
        throwError $ RelocationInvalidAddend (show (Elf.relType rel)) (toInteger addend) sym
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = 0
                         , relocationIsRel      = False
                         , relocationSize       = 4
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = True
                         }
    Elf.R_ARM_COPY -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      when (addend /= 0) $ do
        throwError $ RelocationUnsupportedType (show (Elf.relType rel))
      pure $ Relocation { relocationSym        = sym
                        , relocationOffset     = 0
                        , relocationIsRel      = False
                        , relocationSize       = 4
                        , relocationIsSigned   = False
                        , relocationEndianness = end
                        , relocationJumpSlot   = False
                        }
    tp -> do
      throwError $ RelocationUnsupportedType (show tp)



-- | Attempt to resolve an X86_64 specific symbol.
relaTargetARM64 :: Endianness
                   -- ^ Endianness of relocations
                -> Maybe SegmentIndex
                   -- ^ Index of segment for dynamic relocations
                -> SymbolTable 64 -- ^ Symbol table
                -> Elf.RelEntry Elf.AArch64_RelocationType -- ^ Relocaiton entry
                -> MemWord 64
                   -- ^ Addend of symbol
                -> RelFlag
                -> SymbolResolver (Relocation 64)
relaTargetARM64 end msegIndex symtab rel addend relFlag =
  case Elf.relType rel of
    Elf.R_AARCH64_ABS64 -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend
                         , relocationIsRel      = False
                         , relocationSize       = 8
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
    Elf.R_AARCH64_GLOB_DAT -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend
                         , relocationIsRel      = False
                         , relocationSize       = 8
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
    Elf.R_AARCH64_RELATIVE -> do
      -- This relocation has the value B(S) + A where
      -- - A is the addend for the relocation, and
      -- - B(S) with S ≠ 0 resolves to the difference between the
      --   address at which the segment defining the symbol S was
      --   loaded and the address at which it was linked.
      --  - B(S) with S = 0 resolves to the difference between the
      --    address at which the segment being relocated was loaded
      --    and the address at which it was linked.
      --
      -- Since the address at which it was linked is a constant, we
      -- create a non-relative address but subtract the link address
      -- from the offset.

      -- Get the address at which it was linked so we can subtract from offset.
      let linktimeAddr = Elf.relAddr rel

      -- Resolve the symbol using the index in the relocation.
      sym <-
        if Elf.relSym rel == 0 then do
          case msegIndex of
            Nothing -> do
              throwError $ RelocationZeroSymbol
            Just idx ->
              pure $! SegmentBaseAddr idx
        else do
          resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend - fromIntegral linktimeAddr
                         , relocationIsRel      = False
                         , relocationSize       = 8
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }

    Elf.R_AARCH64_JUMP_SLOT -> do
      -- This is a PLT relocation
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      -- For rela entries, check that addend is 0
      -- N.B. Rel entries read from the target bits, and these typically point to the
      -- start of the PLT, but are otherwise ignored for relocation purposes.
      when (relFlag == IsRela && addend /= 0) $ do
        throwError $ RelocationInvalidAddend (show (Elf.relType rel)) (toInteger addend) sym
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = 0
                         , relocationIsRel      = False
                         , relocationSize       = 8
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = True
                         }
    tp -> do
      throwError $ RelocationUnsupportedType (show tp)

-- | Attempt to resolve a PPC32-specific symbol.
relaTargetPPC32 :: Endianness
                -- ^ Endianness of relocations
                -> Maybe SegmentIndex
                -- ^ Index of segment for dynamic relocations
                -> SymbolTable 32 -- ^ Symbol table
                -> Elf.RelEntry Elf.PPC32_RelocationType -- ^ Relocation entry
                -> MemWord 32
                -- ^ Addend of symbol
                -> RelFlag
                -> SymbolResolver (Relocation 32)
relaTargetPPC32 end msegIndex symtab rel addend _relFlag =
  case Elf.relType rel of
    Elf.R_PPC_ADDR32 -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend
                         , relocationIsRel      = False
                         , relocationSize       = 4
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
    Elf.R_PPC_GLOB_DAT -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend
                         , relocationIsRel      = False
                         , relocationSize       = 4
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
    Elf.R_PPC_RELATIVE -> do
      -- This relocation has the value B + A where
      -- - A is the addend for the relocation, and
      -- - B resolves to the difference between the
      --   address at which the segment defining the symbol was
      --   loaded and the address at which it was linked.
      --
      -- Since the address at which it was linked is a constant, we
      -- create a non-relative address but subtract the link address
      -- from the offset.

      -- Get the address at which it was linked so we can subtract from offset.
      let linktimeAddr = Elf.relAddr rel

      -- Resolve the symbol using the index in the relocation.
      sym <-
        if Elf.relSym rel == 0 then do
          case msegIndex of
            Nothing -> do
              throwError $ RelocationZeroSymbol
            Just idx ->
              pure $! SegmentBaseAddr idx
        else do
          resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend - fromIntegral linktimeAddr
                         , relocationIsRel      = False
                         , relocationSize       = 4
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
    Elf.R_PPC_JMP_SLOT -> do
      -- This is a PLT relocation
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend
                         , relocationIsRel      = False
                         , relocationSize       = 4
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = True
                         }
    tp ->
      throwError $ RelocationUnsupportedType (show tp)

-- | Attempt to resolve a PPC64-specific symbol.
relaTargetPPC64 :: Endianness
                -- ^ Endianness of relocations
                -> Maybe SegmentIndex
                -- ^ Index of segment for dynamic relocations
                -> SymbolTable 64 -- ^ Symbol table
                -> Elf.RelEntry Elf.PPC64_RelocationType -- ^ Relocation entry
                -> MemWord 64
                -- ^ Addend of symbol
                -> RelFlag
                -> SymbolResolver (Relocation 64)
relaTargetPPC64 end msegIndex symtab rel addend _relFlag =
  case Elf.relType rel of
    Elf.R_PPC64_ADDR64 -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend
                         , relocationIsRel      = False
                         , relocationSize       = 8
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
    Elf.R_PPC64_GLOB_DAT -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend
                         , relocationIsRel      = False
                         , relocationSize       = 8
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
    Elf.R_PPC64_RELATIVE -> do
      -- This relocation has the value B + A where
      -- - A is the addend for the relocation, and
      -- - B resolves to the difference between the
      --   address at which the segment defining the symbol was
      --   loaded and the address at which it was linked.
      --
      -- Since the address at which it was linked is a constant, we
      -- create a non-relative address but subtract the link address
      -- from the offset.

      -- Get the address at which it was linked so we can subtract from offset.
      let linktimeAddr = Elf.relAddr rel

      -- Resolve the symbol using the index in the relocation.
      sym <-
        if Elf.relSym rel == 0 then do
          case msegIndex of
            Nothing -> do
              throwError $ RelocationZeroSymbol
            Just idx ->
              pure $! SegmentBaseAddr idx
        else do
          resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend - fromIntegral linktimeAddr
                         , relocationIsRel      = False
                         , relocationSize       = 8
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
    Elf.R_PPC64_JMP_SLOT -> do
      -- This is a PLT relocation
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend
                         , relocationIsRel      = False
                         , relocationSize       = 8
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = True
                         }
    tp ->
      throwError $ RelocationUnsupportedType (show tp)

toEndianness :: Elf.ElfData -> Endianness
toEndianness Elf.ELFDATA2LSB = LittleEndian
toEndianness Elf.ELFDATA2MSB = BigEndian

-- | Creates a relocation map from the contents of a dynamic section.
getRelocationResolver
  :: forall w
  .  Elf.ElfHeader w
  -> MemLoader w (SomeRelocationResolver w)
getRelocationResolver hdr =
  case (Elf.headerClass hdr, Elf.headerMachine hdr) of
    (Elf.ELFCLASS64, Elf.EM_X86_64) ->
      pure $ SomeRelocationResolver relaTargetX86_64
    (Elf.ELFCLASS32, Elf.EM_ARM) ->
      pure $ SomeRelocationResolver $ relaTargetARM32 end
    (Elf.ELFCLASS64, Elf.EM_AARCH64) ->
      pure $ SomeRelocationResolver $ relaTargetARM64 end
    (Elf.ELFCLASS32, Elf.EM_PPC) ->
      pure $ SomeRelocationResolver $ relaTargetPPC32 end
    (Elf.ELFCLASS64, Elf.EM_PPC64) ->
      pure $ SomeRelocationResolver $ relaTargetPPC64 end
    (_,mach) -> throwError $ UnsupportedArchitecture (show mach)
  where
    end = toEndianness (Elf.headerData hdr)

resolveRela :: ( MemWidth w
               , Elf.RelocationWidth tp ~ w
               , Elf.IsRelocationType tp
               , Integral (Elf.ElfIntType w)
               )
            => SymbolTable w
            -> RelocationResolver tp
            -> Integer -- ^ Index of relocation
            -> Elf.RelaEntry tp
            -> ResolveFn (MemLoader w) w
resolveRela symtab resolver _relaIdx rela msegIdx _ = do
  er <- runSymbolResolver $
          resolver msegIdx symtab (Elf.relaToRel rela) (fromIntegral (Elf.relaAddend rela)) IsRela
  case er of
    Left e -> do
      addWarning (IgnoreRelocation e)
      pure Nothing
    Right r ->
      pure $ Just r

resolveRel :: ( MemWidth w
              , Elf.RelocationWidth tp ~ w
              , Elf.IsRelocationType tp
              )
           => Endianness -- ^ Endianness of Elf file
           -> SymbolTable w -- ^ Symbol table
           -> RelocationResolver tp
           -> Integer -- ^ Index of relocation
           -> Elf.RelEntry tp
           -> ResolveFn (MemLoader w) w
resolveRel end symtab resolver _relIdx rel msegIdx bytes = do
  -- Get the number of bits in the addend
  let bits = Elf.relocTargetBits (Elf.relType rel)
  -- Compute the addended by masking off the low order bits, and
  -- then sign extending them.
  let mask = (1 `shiftL` (bits - 1)) - 1
  let uaddend = bytesToInteger end bytes .&. mask

  -- Convert uaddend as signed by looking at most-significant bit.
  let saddend | uaddend `testBit` (bits - 1) =
                  uaddend - (1 `shiftL` bits)
              | otherwise =
                  uaddend
  -- Update the resolver.
  er <- runSymbolResolver $ resolver msegIdx symtab rel (fromInteger saddend) IsRel
  case er of
    Left e -> do
      addWarning (IgnoreRelocation e)
      pure Nothing
    Right r -> do
      pure $ Just r

relocTargetBytes :: (Elf.IsRelocationType tp, MemWidth (Elf.RelocationWidth tp))
                 => tp
                 -> MemWord (Elf.RelocationWidth tp)
relocTargetBytes tp = fromIntegral $ (Elf.relocTargetBits tp + 7) `shiftR` 3


-- | Maps address that relocations apply to to the relocation information.
type RelocMap w = Map (MemWord w) (RelocEntry (MemLoader w) w)

-- | Add a relocation entry to the map.
addRelocEntry :: RelocMap w
              -> MemWord w
              -> RelocEntry (MemLoader w) w
              -> MemLoader w (RelocMap w)
addRelocEntry m addr e =
  case Map.insertLookupWithKey (\_k _new old -> old) addr e m of
    (Nothing, m') -> pure m'
    (Just _, _) -> do
      addWarning $ MultipleRelocationsAtAddr (memWordValue addr)
      pure m

-- | Add a relocation entry to the map.
addRelaEntry :: (Elf.IsRelocationType tp, w ~ Elf.RelocationWidth tp)
            => SymbolTable w
            -> RelocationResolver tp
            -> (Integer, RelocMap w)
            -> Elf.RelaEntry tp
            -> MemLoader w (Integer, RelocMap w)
addRelaEntry symtab resolver (idx,m) r = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
    let addr = fromIntegral (Elf.relaAddr r)
        e =  RelocEntry { relocEntrySize = relocTargetBytes (Elf.relaType r)
                        , applyReloc = resolveRela symtab resolver idx r
                        }
    (idx+1,) <$> addRelocEntry m addr e

addRelaEntries :: (Elf.IsRelocationType tp, w ~ Elf.RelocationWidth tp)
              => RelocMap w
              -> SymbolTable w
              -- ^ Map from symbol indices to associated symbol
              -> RelocationResolver tp
                 -- Resolver for relocations
              -> [Elf.RelaEntry tp]
              -- ^ Buffer containing relocation entries in Rel format
              -> MemLoader w (RelocMap w)
addRelaEntries m symtab resolver entries = do
  snd <$> foldlM (addRelaEntry symtab resolver) (0,m) entries

-- | Add rela relocation entries to map.
addElfRelaEntries :: (Elf.IsRelocationType tp, w ~ Elf.RelocationWidth tp)
                  => RelocMap w
                  -> Elf.ElfData
                  -- ^ Endianness
                  -> RelocationResolver tp
                  -> SymbolTable w
                  -- ^ Map from symbol indices to associated symbol
                  -> Maybe BS.ByteString
                  -- ^ Buffer containing relocation entries in Rela format
                  -> MemLoader w (RelocMap w)
addElfRelaEntries m _ _ _ Nothing =
  pure m
addElfRelaEntries m dta resolver symtab (Just relaBuffer) = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
    case Elf.decodeRelaEntries dta relaBuffer of
      Left msg -> do
        addWarning (RelocationParseFailure msg)
        pure m
      Right entries -> do
        addRelaEntries m symtab resolver entries

-- | Add a relocation entry to the map.
addRelEntry :: (Elf.IsRelocationType tp, w ~ Elf.RelocationWidth tp)
            => Endianness
            -> SymbolTable w
            -> RelocationResolver tp
            -> (Integer, RelocMap w)
            -> Elf.RelEntry tp
            -> MemLoader w (Integer, RelocMap w)
addRelEntry end symtab resolver (idx,m) r = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
    let addr = fromIntegral (Elf.relAddr r)
        e =  RelocEntry { relocEntrySize = relocTargetBytes (Elf.relType r)
                        , applyReloc = resolveRel end symtab resolver idx r
                        }
    (idx+1,) <$> addRelocEntry m addr e

addRelEntries :: (Elf.IsRelocationType tp, w ~ Elf.RelocationWidth tp)
              => RelocMap w
              -> Elf.ElfData
              -- ^ Endianness
              -> SymbolTable w
              -- ^ Map from symbol indices to associated symbol
              -> RelocationResolver tp
                 -- Resolver for relocations
              -> [Elf.RelEntry tp]
              -- ^ Buffer containing relocation entries in Rel format
              -> MemLoader w (RelocMap w)
addRelEntries m dta symtab resolver entries =
  snd <$> foldlM (addRelEntry (toEndianness dta) symtab resolver) (0,m) entries

-- | Add rel relocation entries to map.
addElfRelEntries :: (Elf.IsRelocationType tp, w ~ Elf.RelocationWidth tp)
                 => RelocMap w
                 -> Elf.ElfData
                 -- ^ Endianness
                 -> RelocationResolver tp
                 -> SymbolTable w
                 -- ^ Map from symbol indices to associated symbol
                 -> Maybe BS.ByteString
                 -- ^ Buffer containing relocation entries in Rel format
                 -> MemLoader w (RelocMap w)
addElfRelEntries m _ _ _ Nothing =
  pure m
addElfRelEntries m dta resolver symtab (Just relBuffer) = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
    case Elf.decodeRelEntries dta relBuffer of
      Left msg -> do
        addWarning (RelocationParseFailure msg)
        pure Map.empty
      Right entries -> do
        addRelEntries m dta symtab resolver entries

-- | This checks a computation that returns a dynamic error or succeeds.
runDynamic :: Either Elf.DynamicError a -> MemLoader w a
runDynamic (Left e) = throwError (FormatDynamicError e)
runDynamic (Right r) = pure r


-- | Attempt to extract bytestring from region identified by two tags,
-- and call a continuation if succesful or return a default value if not.
withDynamicBytes :: Elf.DynamicMap w -- ^ Dynamic map
                 -> Elf.VirtAddrMap w -- ^ Virtual address map for loading files.
                 -> Elf.ElfDynamicTag -- ^ Offset
                 -> Elf.ElfDynamicTag -- ^ Size
                 -> a -- ^ Value to return if loading fails.
                 -> (BS.ByteString -> MemLoader w a)
                 -- ^ Continutation to run with bytes.
                 -> MemLoader w a
withDynamicBytes dmap virtMap offTag sizeTag failVal cont = do
  case (Map.findWithDefault [] offTag dmap, Map.findWithDefault [] sizeTag dmap) of
    ([off], [sz]) -> do
      w <- uses mlsMemory memAddrWidth
      reprConstraints w $
        case Elf.lookupVirtAddrContents off virtMap of
          Just relocStartBytes
            | toInteger (BS.length relocStartBytes) >= toInteger sz ->
                cont $ BS.take (fromIntegral sz) relocStartBytes
          _ -> do
            addWarning $ DynamicTagsOutOfRange offTag sizeTag (fromIntegral off) (fromIntegral sz)
            pure failVal
    (_:_:_, _) -> do
      addWarning $ DynamicMultipleTags offTag
      pure failVal
    (_, _:_:_) -> do
      addWarning $ DynamicMultipleTags sizeTag
      pure failVal
    ([_], []) -> do
      addWarning $ DynamicTagPairMismatch offTag sizeTag
      pure failVal
    ([], [_]) -> do
      addWarning $ DynamicTagPairMismatch sizeTag offTag
      pure failVal
    ([], []) ->
      pure failVal

-- | Attempt to extract relocations in Android's compressed format
-- from a region identified by two tags, and call a continuation if
-- succesful or return a default value if not.
withAndroidRelaEntries :: ( w ~ Elf.RelocationWidth tp
                          , Elf.IsRelocationType tp
                          )
                       => Elf.DynamicMap w -- ^ Dynamic map
                       -> Elf.VirtAddrMap w -- ^ Virtual address map for loading files.
                       -> Elf.ElfDynamicTag -- ^ Offset
                       -> Elf.ElfDynamicTag -- ^ Size
                       -> a -- ^ Value to return if loading fails.
                       -> (V.Vector (Elf.RelaEntry tp) -> MemLoader w a)
                       -- ^ Continutation to run with bytes.
                       -> MemLoader w a
withAndroidRelaEntries dmap virtMap offTag sizeTag failVal cont =
  withDynamicBytes dmap virtMap offTag sizeTag failVal $ \bytes -> do
    w <- uses mlsMemory memAddrWidth
    reprConstraints w $
      case Elf.decodeAndroidRelaEntries bytes of
        Left e -> do
          addWarning $ AndroidRelDecodingError offTag e
          pure failVal
        Right v ->
          cont v

-- | Create a relocation map from the dynamic loader information.
dynamicRelocationMap :: Elf.ElfHeader w
                     -> V.Vector (Elf.Phdr w)
                     -> BS.ByteString -- ^ Contents of file.
                     -> MemLoader w (Map (MemWord w) (RelocEntry (MemLoader w) w))
dynamicRelocationMap hdr phdrs contents = do
  let dynPhdrs = V.filter (\p -> Elf.phdrSegmentType p == Elf.PT_DYNAMIC) phdrs
  case toList dynPhdrs of
    [] -> pure $ Map.empty
    dynPhdr:dynRest -> do
      when (not (null dynRest)) $ do
        addWarning MultipleDynamicSegments
      w <- uses mlsMemory memAddrWidth
      reprConstraints w $ do
        -- Build virtual address map so that we can resolve
        -- elf virtual addresses to their program header offset.
        let phdrList = V.toList phdrs
        case Elf.virtAddrMap contents phdrList of
          Nothing -> do
            addWarning OverlappingLoadableSegments
            pure Map.empty
          Just virtMap -> do
            let dynContents = slice (Elf.phdrFileRange dynPhdr) contents
            -- Find the dynamic section from the contents.
            dynSection <- runDynamic $
              Elf.dynamicEntries (Elf.headerData hdr) (Elf.headerClass hdr) dynContents
            let dta = Elf.headerData hdr
            SomeRelocationResolver (resolver :: RelocationResolver tp) <- getRelocationResolver hdr
            verDefMap <- runDynamic $ Elf.dynVersionDefMap dynSection virtMap
            verReqMap <- runDynamic $ Elf.dynVersionReqMap dynSection virtMap
            let symtab = DynamicSymbolTable dynSection virtMap verDefMap verReqMap
            -- Parse relocations
            mRelaBuffer <- runDynamic $ Elf.dynRelaBuffer dynSection virtMap
            let rc0 = if isJust mRelaBuffer then 1 else 0
            relocs0 <- addElfRelaEntries Map.empty dta resolver symtab mRelaBuffer

            mRelBuffer  <- runDynamic $ Elf.dynRelBuffer  dynSection virtMap
            let rc1 = if isJust mRelBuffer then 1 else 0
            relocs1 <-addElfRelEntries  relocs0  dta resolver symtab mRelBuffer

            let dmap = Elf.dynMap dynSection
            (rc2,relocs2) <- do
              let relocMap = relocs1
              let offTag  = Elf.DT_ANDROID_RELA
              let sizeTag = Elf.DT_ANDROID_RELASZ
              withAndroidRelaEntries dmap virtMap offTag sizeTag (0,relocMap) $ \entryVec -> do
                let entries = V.toList entryVec
                relocMap' <- addRelaEntries relocMap symtab resolver entries
                pure (1, relocMap')
            (rc3,relocs3) <- do
              let relocMap = relocs2
              let offTag  = Elf.DT_ANDROID_REL
              let sizeTag = Elf.DT_ANDROID_RELSZ
              withAndroidRelaEntries dmap virtMap offTag sizeTag (0,relocMap) $ \entryVec -> do
                when (any (\r -> Elf.relaAddend r /= 0) entryVec) $ do
                  addWarning $ AndroidRelWithNonzeroAddend
                let entries = V.toList $ Elf.relaToRel <$> entryVec
                relocMap' <- addRelEntries relocMap dta symtab resolver entries
                pure (1, relocMap')
            when (rc0 + rc1 + rc2 + rc3 > (1 :: Int)) $ do
              addWarning $ MultipleRelocationTables

            case Elf.dynPLTRel dynSection virtMap of
              Left e -> do
                addWarning $ RelocationParseFailure (show e)
                pure $! relocs1
              Right Elf.PLTEmpty ->
                pure $! relocs1
              Right (Elf.PLTRel entries) ->
                addRelEntries relocs3 dta symtab resolver entries
              Right (Elf.PLTRela entries) ->
                addRelaEntries relocs3 symtab resolver entries

------------------------------------------------------------------------
-- Elf segment loading

reprConstraints :: AddrWidthRepr w
                -> ((Bits (ElfWordType w)
                    , Bounded  (Elf.ElfIntType w)
                    , Integral (Elf.ElfIntType w)
                    , Bounded  (Elf.ElfWordType w)
                    , Integral (Elf.ElfWordType w)
                    , Show (ElfWordType w)
                    , MemWidth w) => a)
                -> a
reprConstraints Addr32 x = x
reprConstraints Addr64 x = x

-- | Load an elf file into memory.
insertElfSegment :: RegionIndex
                    -- ^ Region for elf segment
                 -> Integer
                    -- ^ Amount to add to linktime virtual address for this memory.
                 -> ElfFileSectionMap (Elf.FileOffset (ElfWordType w))
                 -> BS.ByteString
                    -- ^ Contents of elf file
                 -> Map (MemWord w) (RelocEntry (MemLoader w) w)
                    -- ^ Relocations to apply when inserting segment.
                 -> Elf.Phdr w
                 -> MemLoader w ()
insertElfSegment regIdx addrOff shdrMap contents relocMap phdr = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $
   when (Elf.phdrMemSize phdr > 0) $ do
    let segIdx = Elf.phdrSegmentIndex phdr
    seg <- do
      let linkBaseOff = fromIntegral (Elf.phdrSegmentVirtAddr phdr)
      let flags = flagsForSegmentFlags (Elf.phdrSegmentFlags phdr)
      let dta = slice (Elf.phdrFileRange phdr) contents
      let sz = fromIntegral $ Elf.phdrMemSize phdr
      memSegment relocMap regIdx addrOff (Just segIdx) linkBaseOff flags dta sz
    loadMemSegment ("Segment " ++ show segIdx) seg
    let phdrOffset = Elf.phdrFileStart phdr
    let phdrEnd = phdrOffset `Elf.incOffset` Elf.phdrFileSize phdr
    -- Add segment index to address mapping to memory object.
    mlsMemory %= memBindSegmentIndex segIdx seg
    -- Iterative through sections
    let l = IMap.toList $ IMap.intersecting shdrMap (IntervalCO phdrOffset phdrEnd)
    forM_ l $ \(i, elfIdx) -> do
      case i of
        IntervalCO shdr_start _ -> do
          when (phdrOffset > shdr_start) $ do
            error "Found section header that overlaps with program header."
          let sec_offset = fromIntegral $ shdr_start - phdrOffset
          addr <- case resolveSegmentOff seg sec_offset of
                    Just addr -> pure addr
                    Nothing -> error $ "insertElfSegment: Failed to resolve segment offset at "
                                    ++ show sec_offset
          mlsMemory   %= memBindSectionIndex elfIdx addr
          mlsIndexMap %= Map.insert elfIdx addr
        _ -> error "Unexpected shdr interval"

-- | Load an elf file into memory by parsing segments.
memoryForElfSegments'
  :: forall w
  .  RegionIndex
  -> Integer
  -> Elf.ElfHeaderInfo w
  -> Either String (Memory w -- Memory
                   , SectionIndexMap w -- Section index map
                   , [MemLoadWarning] -- Warnings from load
                   )
memoryForElfSegments' regIndex addrOff elf = do
  let hdr = Elf.header elf
  let cl = Elf.headerClass hdr
  let w =  elfAddrWidth cl
  let contents = Elf.headerFileContents elf
  let phdrs = V.generate (fromIntegral (Elf.phdrCount elf)) $ \i ->
                Elf.phdrByIndex elf (fromIntegral i)

  runMemLoader (toEndianness (Elf.headerData hdr)) (emptyMemory w) $ reprConstraints w $ do
      -- Create relocation map
      relocMap <- dynamicRelocationMap hdr phdrs contents
      let intervals :: ElfFileSectionMap (Elf.FileOffset (ElfWordType w))
          intervals = IMap.fromList $
            [ (IntervalCO (Elf.shdrOff shdr) end, idx-1)
            | idx <- [1..Elf.shdrCount elf]
            , let shdr = Elf.shdrByIndex elf (idx-1)
            , let end = Elf.incOffset (Elf.shdrOff shdr) (Elf.shdrFileSize shdr)
            ]
      forM_ phdrs $ \p -> do
        when (Elf.phdrSegmentType p == Elf.PT_LOAD) $ do
          insertElfSegment regIndex addrOff intervals contents relocMap p

-- | Load an elf file into memory by parsing segments.
memoryForElfSegments
  :: forall w
  .  LoadOptions
  -> Elf.ElfHeaderInfo w
  -> Either String (Memory w -- Memory
                   , SectionIndexMap w -- Section index map
                   , [MemLoadWarning] -- Warnings from load
                   )
memoryForElfSegments opt elf = do
  let regIndex = adjustedLoadRegionIndex (Elf.headerType (Elf.header elf)) opt
  let addrOff = loadRegionBaseOffset opt
  memoryForElfSegments' regIndex addrOff elf

------------------------------------------------------------------------
-- Elf section loading

-- | Contains the name of a section we allocate and whether
-- relocations are used.
type AllocatedSectionInfo = (BS.ByteString, Bool)

allocatedNames :: AllocatedSectionInfo -> [BS.ByteString]
allocatedNames (nm,False) = [nm]
allocatedNames (nm,True) = [nm, ".rela" <> nm]

allocatedSectionInfo :: [AllocatedSectionInfo]
allocatedSectionInfo =
  [ (,) ".text"     True
  , (,) ".eh_frame" True
  , (,) ".data"     True
  , (,) ".bss"      False
  , (,) ".rodata"   True
  ]

allowedSectionNames :: Set BS.ByteString
allowedSectionNames = Set.fromList
  $ concatMap allocatedNames allocatedSectionInfo
  ++ [ ""
     , ".text.hot"
     , ".text.unlikely"
     , ".tbss"
     , ".tdata", ".rela.tdata"
     , ".comment"
     , ".note.GNU-stack"
     , ".shstrtab"
     , ".symtab"
     , ".strtab"
     , ".llvm_addrsig"
     ]

-- | Map from section names to index and section header.
type ShdrNameMap w =  Map SectionName [(Word16, Elf.Shdr Word32 (ElfWordType w))]

findShdr ::ShdrNameMap w
         -> SectionName
         -> MemLoader w (Maybe (Word16, Elf.Shdr Word32 (ElfWordType w)))
findShdr shdrMap nm =
  case Map.lookup nm shdrMap of
    Nothing -> pure Nothing
    Just [] -> pure Nothing
    Just (s:rest) -> do
      when (not (null rest)) $ do
        addWarning $ MultipleSectionsWithName nm
      pure (Just s)

shdrData :: Integral w => BS.ByteString -> Elf.Shdr nm w -> BS.ByteString
shdrData contents shdr = slice (Elf.shdrFileRange shdr) contents

-- | Add a section to the current memory
insertAllocatedShdr :: Elf.ElfHeader w
                    -> BS.ByteString -- ^ File contents
                    -> SymbolTable w
                    -> ShdrNameMap w
                    -> RegionIndex
                       -- ^ Region for section (should be unique)
                    -> SectionName
                       -- ^ Name of section
                    -> MemLoader w ()
insertAllocatedShdr hdr contents symtab shdrMap regIdx nm = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
   mshdr <- findShdr shdrMap nm
   case mshdr of
    Nothing -> pure ()
    Just (idx, shdr) -> do
      mRelBuffer  <- fmap (fmap (shdrData contents . snd)) $ findShdr shdrMap (".rel" <> nm)
      mRelaBuffer <- fmap (fmap (shdrData contents . snd)) $ findShdr shdrMap (".rela" <> nm)
      -- Build relocation map
      -- Get size of section
      let secSize = Elf.shdrSize shdr
      -- Check if we should load section
      when (not (Elf.shdrFlags shdr `Elf.hasPermissions` Elf.shf_alloc)) $ do
        addWarning $ SectionNotAlloc nm
      when (secSize > 0) $ do
        -- Get base address
        let base = Elf.shdrAddr shdr
        -- Get section flags
        let flags = flagsForSectionFlags (Elf.shdrFlags shdr)
        -- Get bytes in section
        let bytes = shdrData contents shdr
        -- Create memory segment
        SomeRelocationResolver resolver <- getRelocationResolver hdr
        when (isJust mRelBuffer && isJust mRelaBuffer) $ do
          addWarning $ MultipleRelocationTables
        relocMap <- do
          let dta = Elf.headerData hdr
          m1 <- addElfRelaEntries Map.empty dta resolver symtab mRelaBuffer
          addElfRelEntries        m1        dta resolver symtab mRelBuffer
        seg <-
          memSegment relocMap regIdx 0 Nothing (fromIntegral base) flags bytes (fromIntegral secSize)
        -- Load memory segment.
        loadMemSegment ("Section " ++ BSC.unpack nm) seg
        -- Add entry to map elf section index to start in segment.
        addr <- case resolveSegmentOff seg 0 of
                  Just addr -> pure addr
                  Nothing -> error "insertAllocatedShdr: Failed to resolve starting segment offset"
        mlsMemory   %= memBindSectionIndex idx addr
        mlsIndexMap %= Map.insert idx addr

-- | Find and get static symbol table entries from an ELF binary.
elfStaticSymbolTable :: Integral (ElfWordType w)
                     => Elf.ElfHeaderInfo w
                     -> Maybe (V.Vector (Elf.SymtabEntry BS.ByteString (ElfWordType w)))
elfStaticSymbolTable elf = do
  symtab <- Elf.decodeHeaderSymtab elf
  case symtab of
    Left _ -> Nothing
    Right v -> Just (Elf.symtabEntries v)

-- | Find and get dynamic symbol table entries from an ELF binary.
elfDynamicSymbolTable :: Integral (ElfWordType w)
                      => Elf.ElfHeaderInfo w
                      -> Maybe (V.Vector (Elf.SymtabEntry BS.ByteString (ElfWordType w)))
elfDynamicSymbolTable elf = do
  symtab <- Elf.decodeHeaderDynsym elf
  case symtab of
    Left _ -> Nothing
    Right v -> Just (Elf.symtabEntries v)

-- | Load allocated Elf sections into memory.
--
-- This is only used for object files.
memoryForElfSections :: forall w
                     .  Elf.ElfHeaderInfo w
                     -> Either String (Memory w, SectionIndexMap w, [MemLoadWarning])
memoryForElfSections elf = reprConstraints (elfAddrWidth (Elf.headerClass (Elf.header elf))) $ do
  let hdr = Elf.header elf
  let contents = Elf.headerFileContents elf
  let shdrs = Elf.headerShdrs elf

  -- Get string table for section header table.
  let (_, shstrtab) = Elf.shstrtabRangeAndData elf

  let shdrMap :: ShdrNameMap w
      shdrMap = V.ifoldl' insSec Map.empty shdrs
        where insSec m idx shdr =
                case Elf.lookupString (Elf.shdrName shdr) shstrtab of
                  Left _ -> m
                  Right nm ->
                    Map.insertWith (\new old -> old ++ new) nm [(fromIntegral idx, shdr)] m

  let symtab =
        case elfStaticSymbolTable elf of
          Nothing -> NoSymbolTable
          Just v -> StaticSymbolTable v
  -- Create memory for elf sections
  memoryForElfSections' hdr contents shdrMap symtab

-- | Load allocated Elf sections into memory.
--
-- This is only used for object files.  This version uses low-level types
-- for less complex parsing.
memoryForElfSections' :: forall w
                      .  Elf.ElfHeader w -- ^ Header for elf
                      -> BS.ByteString
                      -> ShdrNameMap    w -- ^ Map from section names to section headers
                      -> SymbolTable w -- ^ Symbol table for names.
                      -> Either String (Memory w, SectionIndexMap w, [MemLoadWarning])
memoryForElfSections' hdr contents shdrMap symtab =
  runMemLoader (toEndianness (Elf.headerData hdr)) (emptyMemory (elfAddrWidth (Elf.headerClass hdr))) $ do
    -- Insert sections
    forM_ (zip [1..] allocatedSectionInfo) $ \(idx, (nm,_)) -> do
      insertAllocatedShdr hdr contents symtab shdrMap idx nm
    -- TODO: Figure out what to do about .tdata and .tbss
    -- Check for other section names that we do not support."
    let unsupportedKeys = Map.keysSet shdrMap `Set.difference ` allowedSectionNames
    forM_ unsupportedKeys $ \k -> do
      addWarning $ UnsupportedSection k

------------------------------------------------------------------------
-- Index for elf

-- | Return default region index to use when loading.
adjustedLoadRegionIndex :: Elf.ElfType -> LoadOptions -> RegionIndex
adjustedLoadRegionIndex tp loadOpts =
  case loadOffset loadOpts of
    Just _ -> 0
    Nothing ->
      case tp of
        Elf.ET_REL -> 1
        -- This is only for non-position independent exectuables.
        Elf.ET_EXEC -> 0
        -- This is for shared libraries or position-independent executablkes.
        Elf.ET_DYN -> 1
        _ -> 0

------------------------------------------------------------------------
-- Memory symbol

-- | Type for representing a symbol that has a defined location in
-- this memory.
data MemSymbol w = MemSymbol { memSymbolName :: !BS.ByteString
                               -- ^ Name of symbol
                             , memSymbolStart :: !(MemSegmentOff w)
                               -- ^ Address that symbol starts up.
                             , memSymbolSize :: !(MemWord w)
                               -- ^ Size of symbol as defined in table.
                             }

instance Eq (MemSymbol w) where
  x == y = memSymbolStart x == memSymbolStart y
        && memSymbolName  x == memSymbolName  y
        && memSymbolSize  x == memSymbolSize  y

-- Sort by address, size, then name
instance Ord (MemSymbol w) where
  compare x y
    =  compare (memSymbolStart x) (memSymbolStart y)
    <> compare (memSymbolSize  x) (memSymbolSize  y)
    <> compare (memSymbolName  x) (memSymbolName  y)

------------------------------------------------------------------------
-- memoryForElf

elfHeaderConstraints :: Elf.ElfHeaderInfo w
                     ->  ((Bits (ElfWordType w)
                          , Bounded  (Elf.ElfIntType w)
                          , Integral (Elf.ElfIntType w)
                          , Bounded  (Elf.ElfWordType w)
                          , Integral (Elf.ElfWordType w)
                          , Show (ElfWordType w)
                          , MemWidth w) => a)
                     -> a
elfHeaderConstraints elf = reprConstraints (elfAddrWidth (Elf.headerClass (Elf.header elf)))

{-# DEPRECATED memoryForElf' "Use memoryForElf" #-}
memoryForElf' :: LoadOptions
              -> Elf.ElfHeaderInfo w
              -> (Elf.SymtabEntry BS.ByteString (ElfWordType w) -> Bool)
              -- ^ Filter on symbol table entries
              -> Either String  ( Memory w
                                , [MemSymbol w] -- Function symbols
                                , [MemLoadWarning]
                                , [SymbolResolutionError]
                                )
memoryForElf' opt elf isRelevant = elfHeaderConstraints elf $ do
  let shdrs = Elf.headerShdrs elf
  -- Get the elf memory, section map, warnings based on type.
  (mem, secMap, warnings) <-
    case Elf.headerType (Elf.header elf) of
      -- We load object files by section
      Elf.ET_REL -> do
        when (isJust (loadOffset opt)) $ do
          Left $ "Object file sections have multiple offsets, and do not support loading at address."
        memoryForElfSections elf
      Elf.ET_EXEC ->
        memoryForElfSegments opt elf
      -- Dynamic include dynamic information
      _ ->
        memoryForElfSegments opt elf
  -- Get dynamic symbol table entries
  -- Resolve elf symbol table information
  let (symErrs, funcSymbols) = resolveElfFuncSymbols mem shdrs secMap isRelevant elf
  pure (mem, funcSymbols, warnings, symErrs)

-- | Load allocated Elf sections into memory, using the section table
-- information map.
--
-- Normally, Elf uses segments for loading, but the section
-- information tends to be more precise.
--
-- The return value includes a list of all function symbols (STT_FUNC
-- Symbol table entry types).
memoryForElf :: LoadOptions
             -> Elf.ElfHeaderInfo w
             -> Either String ( Memory w
                              , [MemSymbol w] -- Function symbols
                              , [MemLoadWarning]
                              , [SymbolResolutionError]
                              )
memoryForElf opt elf =
  let isRelevant ste = Elf.steType ste == Elf.STT_FUNC
   in memoryForElf' opt elf isRelevant

-- | Load allocated Elf sections into memory, using the section table
-- information map.
--
-- Normally, Elf uses segments for loading, but the section
-- information tends to be more precise.
--
-- The return value includes a list of *all* symbols, whether they
-- are functions or not.
memoryForElfAllSymbols :: LoadOptions
                       -> Elf.ElfHeaderInfo w
                       -> Either String ( Memory w
                                        , [MemSymbol w] -- Function symbols
                                        , [MemLoadWarning]
                                        , [SymbolResolutionError]
                                        )
memoryForElfAllSymbols opt elf = memoryForElf' opt elf (\_ -> True)

------------------------------------------------------------------------
-- Elf symbol utilities

-- | Error when resolving symbols.
data SymbolResolutionError
   = EmptySymbolName !Int !Elf.ElfSymbolType
     -- ^ Symbol names must be non-empty
   | UndefSymbol !BSC.ByteString
     -- ^ Symbol was in the undefined section.
   | CouldNotResolveAddr !BSC.ByteString
     -- ^ Symbol address could not be resolved.
   | MultipleSymbolTables
     -- ^ The elf file contained multiple symbol tables

instance Show SymbolResolutionError where
  show (EmptySymbolName idx tp ) =
    "Symbol Num " ++ show idx ++ " " ++ show tp ++ " has an empty name."
  show (UndefSymbol nm) = "Symbol " ++ BSC.unpack nm ++ " is in the text section."
  show (CouldNotResolveAddr sym) = "Could not resolve address of " ++ BSC.unpack sym ++ "."
  show MultipleSymbolTables = "Elf contains multiple symbol tables."


-- | Map a symbol table entry in .symtab to the associated symbol information.
--
-- This drops undefined symbols by returning `Nothing, and returns
-- either the symbol information or an error message if we cannot
-- resolve the address.
resolveElfSymbol :: Integral (ElfWordType w)
                 => Memory w -- ^ Memory object from Elf file.
                 -> SymbolAddrResolver w -- ^ Section index mp from memory
                 -> Int -- ^ Index of symbol
                 -> Elf.SymtabEntry BS.ByteString (ElfWordType w)
                 -> Maybe (Either SymbolResolutionError (MemSymbol w))
resolveElfSymbol mem resolver idx ste
    -- Check symbol is defined
  | Elf.steIndex ste == Elf.SHN_UNDEF = Nothing
  -- Check symbol name is non-empty
  | Elf.steName ste == "" = Just $ Left $ EmptySymbolName idx (Elf.steType ste)
  -- Lookup absolute symbol
  | Elf.steIndex ste == Elf.SHN_ABS = reprConstraints (memAddrWidth mem) $ do
      let val = Elf.steValue ste
      case resolveAbsoluteAddr mem (fromIntegral val) of
        Just addr -> Just $ Right $
          MemSymbol { memSymbolName = Elf.steName ste
                    , memSymbolStart = addr
                    , memSymbolSize = fromIntegral (Elf.steSize ste)
                    }
        Nothing   -> Just $ Left $ CouldNotResolveAddr (Elf.steName ste)
  -- Lookup symbol stored in specific section
  | secIdx <- Elf.fromElfSectionIndex (Elf.steIndex ste)
  , secIdx < symSecCount resolver
  , Just addr <- symResolver resolver secIdx (Elf.steValue ste) = addrWidthClass (memAddrWidth mem) $
      Just $ Right $ MemSymbol { memSymbolName = Elf.steName ste
                               , memSymbolStart = addr
                               , memSymbolSize = fromIntegral (Elf.steSize ste)
                               }

  | otherwise = Just $ Left $ CouldNotResolveAddr (Elf.steName ste)

data ResolvedSymbols w = ResolvedSymbols { resolutionErrors :: ![SymbolResolutionError]
                                         , resolvedSymbols :: !(Set (MemSymbol w))
                                         }

instance Semigroup (ResolvedSymbols w) where
  x <> y = ResolvedSymbols { resolutionErrors = resolutionErrors x <> resolutionErrors y
                           , resolvedSymbols   = resolvedSymbols x <> resolvedSymbols y
                           }

instance Monoid (ResolvedSymbols w) where
  mempty = ResolvedSymbols { resolutionErrors = []
                           , resolvedSymbols = Set.empty
                           }

resolutionError :: SymbolResolutionError -> ResolvedSymbols w
resolutionError e = mempty { resolutionErrors = [e] }

resolvedSymbol :: MemSymbol w -> ResolvedSymbols w
resolvedSymbol s = mempty { resolvedSymbols = Set.singleton s }

-- | Construct a resolve symbol entry.
ofResolvedSymbol :: Maybe (Either SymbolResolutionError (MemSymbol w))
                 -> ResolvedSymbols w
ofResolvedSymbol Nothing = mempty
ofResolvedSymbol (Just (Left e)) = resolutionError e
ofResolvedSymbol (Just (Right s)) = resolvedSymbol s

-- | Resolve symbol table entries defined in this Elf file to
-- a mem symbol.
resolveElfFuncSymbols
  :: forall w
  .  (MemWidth w, Integral (ElfWordType w))
  => Memory w
     -- ^ Memory loaded
  -> V.Vector (Elf.Shdr Word32 (Elf.ElfWordType w))
     -- ^ Section headers for symbol table
  -> SectionIndexMap w
     -- ^ Map from s
  -> (Elf.SymtabEntry BS.ByteString (ElfWordType w) -> Bool)
     -- ^ Filter on symbol table entries
  -> Elf.ElfHeaderInfo w
     -- ^ elf header information
  -> ([SymbolResolutionError], [MemSymbol w])
resolveElfFuncSymbols mem shdrs secMap p elf =
   let resolver = mkSymbolAddrResolver shdrs secMap

       staticEntries =
         case elfStaticSymbolTable elf of
           Nothing -> []
           Just v -> V.toList $ V.imap (\i s-> (i, s)) v

       dynamicEntries =
         case elfDynamicSymbolTable elf of
           Nothing -> []
           Just v -> V.toList $ V.imap (\i s-> (i, s)) v

       allEntries :: [(Int, Elf.SymtabEntry BS.ByteString (ElfWordType w))]
       allEntries = staticEntries ++ dynamicEntries

       r :: ResolvedSymbols w
       r = mconcat
         $ fmap (\(idx, s) -> ofResolvedSymbol (resolveElfSymbol mem resolver idx s))
         $ filter (\(_,s) -> p s) allEntries

   in (resolutionErrors r, Set.toList (resolvedSymbols r))

------------------------------------------------------------------------
-- resolveElfContents

-- | Return the segment offset of the elf file entry point or fail if undefined.
getElfEntry ::  LoadOptions
            -> Memory w
            -> RegionIndex
            -> Elf.ElfHeader w
            -> ([String], Maybe (MemSegmentOff w))
getElfEntry loadOpts mem regIdx hdr =  addrWidthClass (memAddrWidth mem) $ do
  Elf.elfClassInstances (Elf.headerClass hdr) $ do
    let adjAddr =
          case loadOffset loadOpts of
            Nothing -> toInteger (Elf.headerEntry hdr)
            Just o -> toInteger o + toInteger (Elf.headerEntry hdr)
    case resolveRegionOff mem regIdx (fromInteger adjAddr) of
      Nothing ->
        ( ["Could not resolve entry point: " ++ showHex (Elf.headerEntry hdr) ""]
        , Nothing
        )
      Just v  -> ([], Just v)

-- | This interprets the Elf file to construct the initial memory,
-- entry points, and functions symbols.
--
-- If it encounters a fatal error it returns the error message in the
-- left value, and otherwise it returns the interpreted information as
-- a 4-tuple of: warnings, the initial memory image, possible entry
-- points (e.g. for an executable or shared library), and function
-- symbols.
resolveElfContents :: LoadOptions
                        -- ^ Options for loading contents
                   -> Elf.ElfHeaderInfo w
                   -> Either String
                             ( [String] -- Warnings
                             , Memory w -- Initial memory
                             , Maybe (MemSegmentOff w) -- Entry point(s)
                             , [MemSymbol w] -- Function symbols
                             )
resolveElfContents loadOpts elf = do
  let hdr = Elf.header elf
  let regIdx = adjustedLoadRegionIndex (Elf.headerType hdr) loadOpts
  case Elf.headerType hdr of
    Elf.ET_REL -> do
      (mem, funcSymbols, warnings, symErrs) <- memoryForElf loadOpts elf
      pure (fmap show warnings ++ fmap show symErrs, mem, Nothing, funcSymbols)
    Elf.ET_EXEC -> do
      (mem, funcSymbols, warnings, symErrs) <- memoryForElf loadOpts elf
      let (entryWarn, mentry) = getElfEntry loadOpts mem regIdx hdr
      Right (fmap show warnings ++ fmap show symErrs ++ entryWarn, mem, mentry, funcSymbols)
    Elf.ET_DYN -> do
      -- This is a shared library or position-independent executable.
      (mem, funcSymbols, warnings, symErrs) <- memoryForElf loadOpts elf
      let (entryWarn, mentry) = getElfEntry loadOpts mem regIdx hdr
      pure (fmap show warnings ++ fmap show symErrs ++ entryWarn, mem, mentry, funcSymbols)
    Elf.ET_CORE ->
      Left "No support for loading core files (Macaw)."
    tp ->
      Left $ "No support for loading ELF files with type " ++ show tp ++ " (Macaw)."
