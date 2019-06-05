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
  ( SectionIndexMap
  , memoryForElf'
  , memoryForElf
  , memoryForElfAllSymbols
  , MemLoadWarning(..)
  , resolveElfContents
  , elfAddrWidth
  , adjustedLoadRegionIndex
    -- * Symbols
  , MemSymbol(..)
    -- * Re-exports
  , module Data.Macaw.Memory.LoadCommon
  , module Data.Macaw.Memory
  , module Data.Macaw.Memory.Symbols
  ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Data.Bits
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as L
import           Data.Either
import           Data.ElfEdit
  ( ElfWordType
  , ElfIntType
  , Elf
  , elfSections
  , elfLayout

  , ElfClass(..)
  , elfClass

  , ElfSection
  , ElfSectionIndex(..)
  , elfSectionIndex
  , ElfSectionFlags
  , elfSectionFlags
  , elfSectionName
  , elfSectionFileSize
  , elfSectionAddr
  , elfSectionData

  , ElfSegmentFlags
  , elfLayoutBytes

  , ElfSymbolTableEntry
  )
import qualified Data.ElfEdit as Elf
import           Data.IntervalMap.Strict (Interval(..), IntervalMap)
import qualified Data.IntervalMap.Strict as IMap
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Semigroup
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import           Data.Word
import           Numeric (showHex)
import           Data.Int

import           Data.Macaw.Memory
import           Data.Macaw.Memory.LoadCommon
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Memory.Symbols

import           Prelude


-- | Return a subrange of a bytestring.
sliceL :: Integral w => Elf.Range w -> L.ByteString -> L.ByteString
sliceL (i,c) = L.take (fromIntegral c) . L.drop (fromIntegral i)

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
type SectionIndexMap w = Map ElfSectionIndex (MemSegmentOff w, ElfSection (ElfWordType w))

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
   | RelocationInvalidAddend !String !Integer
     -- ^ The relocation type given does not allow the adddend with the given value.
   | RelocationDynamicError Elf.DynamicError
     -- ^ Parsing the dynamic section failed when resolving a symbol.

instance Show RelocationError where
  show MissingSymbolTable =
    "Relocations cannot be applied due to missing symbol table."
  show RelocationZeroSymbol =
    "A relocation entry referred to invalid 0 symbol index."
  show (RelocationBadSymbolIndex idx) =
    "A relocation entry referred to invalid symbol index " ++ show idx ++ "."
  show (RelocationUnsupportedType _tp) =
    "Unsupported relocation type."
  show RelocationFileUnsupported =
    "Do not support relocations referring to file entry."
  show (RelocationInvalidAddend tp v) =
    "Do not support addend of " ++ show v ++ " with relocation type " ++ tp ++ "."
  show (RelocationDynamicError e) = show e

------------------------------------------------------------------------
-- MemLoader

type SectionName = BS.ByteString

data MemLoadWarning
  = SectionNotAlloc !SectionName
  | MultipleSectionsWithName !SectionName
  | MultipleDynamicSegments
  | OverlappingLoadableSegments
  | RelocationParseFailure !String
  | DynamicRelaAndRelPresent
    -- ^ Issued if the dynamic section contains table for DT_REL and
    -- DT_RELA.
  | SectionRelaAndRelPresent !BS.ByteString
    -- ^ @SectionRelaAndRelPresent nm@ is issued if we encounter
    -- both section ".rela$nm" and ".rel$nm".
  | UnsupportedSection !SectionName
  | UnknownDefinedSymbolBinding   !SymbolName Elf.ElfSymbolBinding
  | UnknownDefinedSymbolType      !SymbolName Elf.ElfSymbolType
  | UnknownUndefinedSymbolBinding !SymbolName Elf.ElfSymbolBinding
  | UnknownUndefinedSymbolType    !SymbolName Elf.ElfSymbolType
  | ExpectedSectionSymbolNameEmpty !SymbolName
  | ExpectedSectionSymbolLocal
  | InvalidSectionSymbolIndex !Elf.ElfSectionIndex
  | UnsupportedProcessorSpecificSymbolIndex !SymbolName !ElfSectionIndex
  | IgnoreRelocation !Integer !String !RelocationError
    -- ^ @IgnoreRelocation idx tp err@ warns we ignored the location at index @idx@ due to @err@.
    --
    -- @tp@ is a string representing the type which we print, because usually errors come because
    -- we don't support that type or only partially implement it.

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
  show (RelocationParseFailure msg) =
    "Error parsing relocations: " ++ msg
  show DynamicRelaAndRelPresent =
    "PT_DYNAMIC segment contains contain offsets for both DT_REL and DT_RELA relocation tables; "
    ++ " Using only DT_RELA relocations."
  show (SectionRelaAndRelPresent (BSC.unpack -> nm)) =
    "File contains both .rela" ++ nm ++ " and .rel" ++ nm
    ++ " sections; Using only .rela" ++ nm ++ " sections."
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
  show (IgnoreRelocation idx typeName err) =
    "Ignoring relocation " ++ show idx ++ " with type " ++ typeName ++ ": " ++ show err

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
         Right mls -> Right (mls^.mlsMemory, mls^.mlsIndexMap, reverse (mlsWarnings mls))

-- | This adds a Macaw mem segment to the memory
loadMemSegment :: MemWidth w => String -> MemSegment w -> MemLoader w ()
loadMemSegment nm seg =
  StateT $ \mls -> do
    case insertMemSegment seg (mls^.mlsMemory) of
      Left e ->
        throwError $ LoadInsertError nm e
      Right mem' -> do
        pure ((), mls & mlsMemory .~ mem')

-- | Maps file offsets to the elf section
type ElfFileSectionMap v = IntervalMap v (ElfSection v)

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
-- Defined symbol resolution

resolveDefinedSymbolPrec :: SymbolName -> Elf.ElfSymbolBinding -> SymbolResolver SymbolPrecedence
resolveDefinedSymbolPrec _ Elf.STB_LOCAL =
  pure SymbolLocal
resolveDefinedSymbolPrec _ Elf.STB_WEAK =
  pure SymbolWeak
resolveDefinedSymbolPrec _ Elf.STB_GLOBAL =
  pure SymbolStrong
resolveDefinedSymbolPrec nm bnd = do
  symbolWarning $ UnknownDefinedSymbolBinding nm bnd
  pure SymbolStrong

symbolDefTypeMap :: Map Elf.ElfSymbolType SymbolDefType
symbolDefTypeMap = Map.fromList
  [ (,) Elf.STT_OBJECT    SymbolDefObject
  , (,) Elf.STT_FUNC      SymbolDefFunc
  , (,) Elf.STT_TLS       SymbolDefThreadLocal
  , (,) Elf.STT_GNU_IFUNC SymbolDefIFunc
  , (,) Elf.STT_NOTYPE    SymbolDefNoType
  ]

mkDefinedSymbol :: SymbolName
                -> Elf.ElfSymbolBinding
                -> SymbolDefType
                -> SymbolResolver SymbolBinding
mkDefinedSymbol nm bnd tp = do
  prec <- resolveDefinedSymbolPrec nm bnd
  pure $! DefinedSymbol prec tp

resolveDefinedSymbolDef :: ElfSymbolTableEntry wtp
                        -> SymbolResolver SymbolBinding
resolveDefinedSymbolDef sym = do
  let nm = Elf.steName sym
  let bnd = Elf.steBind sym
  let idx = Elf.steIndex sym
  case Elf.steType sym of
    Elf.STT_SECTION
      | idx < Elf.SHN_LOPROC -> do
          when (nm /= "") $
            symbolWarning $ ExpectedSectionSymbolNameEmpty nm
          when (bnd /= Elf.STB_LOCAL) $
            symbolWarning ExpectedSectionSymbolLocal
          pure $ SymbolSection (Elf.fromElfSectionIndex idx)
      | otherwise -> do
          symbolWarning $ InvalidSectionSymbolIndex idx
          mkDefinedSymbol nm bnd SymbolDefUnknown
    Elf.STT_FILE -> do
      pure $ SymbolFile nm
    tp -> do
      dtp <-
        case Map.lookup tp symbolDefTypeMap of
          Just dtp ->
            pure dtp
          Nothing -> do
            symbolWarning $ UnknownDefinedSymbolType nm tp
            pure SymbolDefUnknown
      mkDefinedSymbol nm bnd dtp

------------------------------------------------------------------------
-- Resolve symbols from elf info

resolveUndefinedSymbolReq :: SymbolName
                          -> Elf.ElfSymbolBinding
                          -> SymbolResolver SymbolRequirement
resolveUndefinedSymbolReq _ Elf.STB_WEAK =
  pure SymbolOptional
resolveUndefinedSymbolReq _ Elf.STB_GLOBAL =
  pure SymbolRequired
resolveUndefinedSymbolReq nm bnd = do
  symbolWarning $ UnknownUndefinedSymbolBinding nm bnd
  pure SymbolRequired

resolveUndefinedSymbolType :: SymbolName -> Elf.ElfSymbolType -> SymbolResolver SymbolUndefType
resolveUndefinedSymbolType nm tp =
  case tp of
    Elf.STT_NOTYPE -> pure SymbolUndefNoType
    Elf.STT_OBJECT -> pure SymbolUndefObject
    Elf.STT_FUNC   -> pure SymbolUndefFunc
    Elf.STT_TLS    -> pure SymbolUndefThreadLocal
    _ -> do
      symbolWarning $ UnknownUndefinedSymbolType nm tp
      pure SymbolUndefNoType

------------------------------------------------------------------------
-- Resolve symbol information

-- | Create a symbol ref from Elf versioned symbol from a shared
-- object or executable.
mkSymbolRef :: ElfSymbolTableEntry wtp
            -> SymbolVersion -- ^ Version to use for symbol.
            -> SymbolResolver SymbolInfo
mkSymbolRef sym ver = seq sym $ seq ver $ do
  let nm = Elf.steName sym
  def <-
    case Elf.steIndex sym of
      Elf.SHN_UNDEF -> do
        UndefinedSymbol
          <$> resolveUndefinedSymbolReq nm (Elf.steBind sym)
          <*> resolveUndefinedSymbolType nm (Elf.steType sym)
      Elf.SHN_ABS -> do
        resolveDefinedSymbolDef sym
      Elf.SHN_COMMON -> do
        resolveDefinedSymbolDef sym
      idx | idx < Elf.SHN_LOPROC -> do
        resolveDefinedSymbolDef sym
      idx -> do
        symbolWarning $ UnsupportedProcessorSpecificSymbolIndex nm idx
        UndefinedSymbol SymbolRequired
          <$> resolveUndefinedSymbolType nm (Elf.steType sym)
  pure $!
    SymbolInfo { symbolName = Elf.steName sym
               , symbolVersion = ver
               , symbolDef = def
               }

------------------------------------------------------------------------
-- SymbolTable

-- | This wraps a callback function that lets users lookup symbol information by index
-- from the Elf file.
--
-- It is implemented using a callback function as the Elf dynamic
-- section doesn't provide an explicit number of symbol table
-- elements, and we decided not to depend on meta data such as section
-- names that could be stripped from executables/shared objects.
newtype SymbolTable = SymbolTable { resolveSymbol :: Word32 -> SymbolResolver SymbolInfo }

 -- | Construct a symbol table that just reports a missing symbol table error on lookups.
noSymTab :: SymbolTable
noSymTab = SymbolTable $ \_symIdx -> throwError MissingSymbolTable

-- | Construct symbol table from a static list of symbol table entries.
staticSymTab :: V.Vector (ElfSymbolTableEntry tp) -> SymbolTable
staticSymTab entries = SymbolTable $ \symIdx -> do
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
          mkSymbolRef (sym { Elf.steName = BSC.take i nm }) ver
        Nothing -> do
          mkSymbolRef sym UnversionedSymbol

-- | Use dynamic section to create symbol table function.
dynamicSymbolTable :: Elf.DynamicSection w -> SymbolTable
dynamicSymbolTable ds = SymbolTable $ \symIdx -> do
  when (symIdx == 0) $
    throwError RelocationZeroSymbol
  case Elf.dynSymEntry ds symIdx of
    Left e -> throwError (RelocationDynamicError e)
    Right (sym, mverId) -> do
      let ver = case mverId of
                  Elf.VersionLocal -> UnversionedSymbol
                  Elf.VersionGlobal -> UnversionedSymbol
                  Elf.VersionSpecific elfVer -> VersionedSymbol (Elf.verFile elfVer) (Elf.verName elfVer)
      mkSymbolRef sym ver

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
  -> SymbolTable
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

-- | This attempts to resolve an index in the symbol table to the
-- identifier information needed to resolve its loaded address.
resolveRelocationSym :: SymbolTable
                      -- ^ A vector mapping symbol indices to the
                      -- associated symbol information.
                      -> Word32
                      -- ^ Index in the symbol table this refers to.
                      -> SymbolResolver SymbolIdentifier
resolveRelocationSym symtab symIdx = do
  sym <- resolveSymbol symtab symIdx
  case symbolDef sym of
    DefinedSymbol{} ->
      pure $ SymbolRelocation (symbolName sym) (symbolVersion sym)
    SymbolSection idx ->
      pure $ SectionIdentifier idx
    SymbolFile _ ->
      throwError RelocationFileUnsupported
    UndefinedSymbol{} ->
      pure $ SymbolRelocation (symbolName sym) (symbolVersion sym)

-- | Attempt to resolve an X86_64 specific symbol.
relaTargetX86_64 :: Maybe SegmentIndex
                 -> SymbolTable -- ^ Symbol table to look up symbols in/
                 -> Elf.RelEntry Elf.X86_64_RelocationType
                 -> MemWord 64
                 -- ^ Addend to add to symbol.
                 -> RelFlag
                 -> SymbolResolver (Relocation 64)
relaTargetX86_64 _ symtab rel addend _isRel =
  case Elf.relType rel of

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
    Elf.R_X86_64_32 -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      pure $ Relocation { relocationSym        = sym
                        , relocationOffset     = addend
                        , relocationIsRel      = False
                        , relocationSize       = 4
                        , relocationIsSigned = False
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

    -- Jhx Note. These will be needed to support thread local variables.
    --   Elf.R_X86_64_TPOFF32 -> undefined
    --   Elf.R_X86_64_GOTTPOFF -> undefined

    tp -> throwError $ RelocationUnsupportedType (show tp)

-- | Attempt to resolve an X86_64 specific symbol.
relaTargetARM32 :: Endianness
                 -- ^ Endianness of relocations
              -> Maybe SegmentIndex
                 -- ^ Index of segment for dynamic relocations
              -> SymbolTable -- ^ Symbol table
              -> Elf.RelEntry Elf.ARM32_RelocationType -- ^ Relocaiton entry
              -> MemWord 32
                 -- ^ Addend of symbol
              -> RelFlag
              -> SymbolResolver (Relocation 32)
relaTargetARM32 end msegIndex symtab rel addend relFlag =
  case Elf.relType rel of
    Elf.R_ARM_GLOB_DAT -> do
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      -- Check that least-significant bit of addend is 0 so that we do
      -- not change thumb bit of symbol.
      when (addend `testBit` 0) $ do
        throwError $ RelocationInvalidAddend (show (Elf.relType rel)) (toInteger addend)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = addend
                         , relocationIsRel      = False
                         , relocationSize       = 4
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = False
                         }
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
      let actualAddend =
            case relFlag of
              IsRel -> 0
              IsRela -> addend
      -- Check that addend is 0 so that we do not change thumb bit of symbol.
      when (actualAddend /= 0) $ do
        throwError $ RelocationInvalidAddend (show (Elf.relType rel)) (toInteger actualAddend)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = actualAddend
                         , relocationIsRel      = False
                         , relocationSize       = 4
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = True
                         }
    tp -> do
      throwError $ RelocationUnsupportedType (show tp)

-- | Attempt to resolve an X86_64 specific symbol.
relaTargetARM64 :: Endianness
                   -- ^ Endianness of relocations
                -> Maybe SegmentIndex
                   -- ^ Index of segment for dynamic relocations
                -> SymbolTable -- ^ Symbol table
                -> Elf.RelEntry Elf.ARM64_RelocationType -- ^ Relocaiton entry
                -> MemWord 64
                   -- ^ Addend of symbol
                -> RelFlag
                -> SymbolResolver (Relocation 64)
relaTargetARM64 end _msegIndex symtab rel addend relFlag =
  case Elf.relType rel of
    Elf.R_AARCH64_JUMP_SLOT -> do
      -- This is a PLT relocation
      sym <- resolveRelocationSym symtab (Elf.relSym rel)
      let actualAddend =
            case relFlag of
              IsRel -> 0
              IsRela -> addend
      -- Check that addend is 0
      when (actualAddend /= 0) $ do
        throwError $ RelocationInvalidAddend (show (Elf.relType rel)) (toInteger actualAddend)
      pure $! Relocation { relocationSym        = sym
                         , relocationOffset     = actualAddend
                         , relocationIsRel      = False
                         , relocationSize       = 8
                         , relocationIsSigned   = False
                         , relocationEndianness = end
                         , relocationJumpSlot   = True
                         }
    tp -> do
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
    (Elf.ELFCLASS32, Elf.EM_ARM) -> do
      let end = toEndianness (Elf.headerData hdr)
      pure $ SomeRelocationResolver $ relaTargetARM32 end
    (Elf.ELFCLASS64, Elf.EM_AARCH64) -> do
      let end = toEndianness (Elf.headerData hdr)
      pure $ SomeRelocationResolver $ relaTargetARM64 end
    (_,mach) -> throwError $ UnsupportedArchitecture (show mach)


resolveRela :: ( MemWidth w
               , Elf.RelocationWidth tp ~ w
               , Elf.IsRelocationType tp
               , Integral (Elf.ElfIntType w)
               )
            => SymbolTable
            -> RelocationResolver tp
            -> Integer -- ^ Index of relocation
            -> Elf.RelaEntry tp
            -> ResolveFn (MemLoader w) w
resolveRela symtab resolver relaIdx rela msegIdx _ = do
  er <- runSymbolResolver $
          resolver msegIdx symtab (Elf.relaToRel rela) (fromIntegral (Elf.relaAddend rela)) IsRela
  case er of
    Left e -> do
      addWarning (IgnoreRelocation relaIdx (show (Elf.relaType rela)) e)
      pure Nothing
    Right r -> do
      pure $ Just r

resolveRel :: ( MemWidth w
              , Elf.RelocationWidth tp ~ w
              , Elf.IsRelocationType tp
              )
           => Endianness -- ^ Endianness of Elf file
           -> SymbolTable -- ^ Symbol table
           -> RelocationResolver tp
           -> Integer -- ^ Index of relocation
           -> Elf.RelEntry tp
           -> ResolveFn (MemLoader w) w
resolveRel end symtab resolver relIdx rel msegIdx bytes = do
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
      addWarning (IgnoreRelocation relIdx (show (Elf.relType rel)) e)
      pure Nothing
    Right r -> do
      pure $ Just r

relocTargetBytes :: (Elf.IsRelocationType tp, MemWidth (Elf.RelocationWidth tp))
                 => tp
                 -> MemWord (Elf.RelocationWidth tp)
relocTargetBytes tp = fromIntegral $ (Elf.relocTargetBits tp + 7) `shiftR` 3


relocFromRela :: ( Elf.IsRelocationType tp
                 , w ~ Elf.RelocationWidth tp
                 , MemWidth w
                 , Integral (ElfIntType w)
                 , Integral (ElfWordType w)
                 )
              => SymbolTable
              -> RelocationResolver tp
              -> Integer -- ^ Index of relocation entry for error reporting
              -> Elf.RelaEntry tp
              -> (MemWord w, RelocEntry (MemLoader w) w)
relocFromRela symtab resolver idx r =
  ( fromIntegral (Elf.relaAddr r)
  , RelocEntry { relocEntrySize = relocTargetBytes (Elf.relaType r)
               , applyReloc = resolveRela symtab resolver idx r
               }
  )

relocFromRel :: ( Elf.IsRelocationType tp
                , w ~ Elf.RelocationWidth tp
                , MemWidth w
                , Integral (ElfWordType w)
                )
             => Endianness
             -> SymbolTable
             -> RelocationResolver tp
             -> Integer -- ^ Index of relocation entry for error reporting.
             -> Elf.RelEntry tp
             -> (MemWord w, RelocEntry (MemLoader w) w)
relocFromRel end symtab resolver idx r =
  ( fromIntegral (Elf.relAddr r)
  , RelocEntry { relocEntrySize = relocTargetBytes (Elf.relType r)
               , applyReloc = resolveRel end symtab resolver idx r
               }
  )

relocMapFromRelAndRela :: (Elf.IsRelocationType tp, w ~ Elf.RelocationWidth tp)
                       => Elf.ElfData
                       -- ^ Endianness
                       -> RelocationResolver tp
                       -> SymbolTable
                       -- ^ Map from symbol indices to associated symbol
                       -> Maybe L.ByteString
                       -- ^ Buffer containing relocation entries in Rel format
                       -> Maybe L.ByteString
                       -- ^ Buffer containing relocation entries in Rela format
                       -> MemLoader w (Map (MemWord w) (RelocEntry (MemLoader w) w))
relocMapFromRelAndRela _dta _resolver _symtab Nothing Nothing = do
  pure Map.empty
relocMapFromRelAndRela dta resolver symtab _ (Just relaBuffer) = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
    case Elf.elfRelaEntries dta relaBuffer of
      Left msg -> do
        addWarning (RelocationParseFailure msg)
        pure Map.empty
      Right entries -> do
        pure $ Map.fromList $ zipWith (relocFromRela symtab resolver) [0..]  entries
relocMapFromRelAndRela dta resolver symtab (Just relBuffer) Nothing = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
    case Elf.elfRelEntries dta relBuffer of
      Left msg -> do
        addWarning (RelocationParseFailure msg)
        pure Map.empty
      Right entries -> do
        pure $ Map.fromList $ zipWith (relocFromRel (toEndianness dta) symtab resolver) [0..] entries

-- | This checks a computation that returns a dynamic error or succeeds.
runDynamic :: Either Elf.DynamicError a -> MemLoader w a
runDynamic (Left e) = throwError (FormatDynamicError e)
runDynamic (Right r) = pure r


-- | Create a relocation map from the dynamic loader information.
dynamicRelocationMap :: Elf.ElfHeader w
                     -> [Elf.Phdr w]
                     -> L.ByteString
                     -> MemLoader w (Map (MemWord w) (RelocEntry (MemLoader w) w))
dynamicRelocationMap hdr ph contents =
  case filter (\p -> Elf.phdrSegmentType p == Elf.PT_DYNAMIC) ph of
    [] -> pure $ Map.empty
    dynPhdr:dynRest -> do
      when (not (null dynRest)) $
        addWarning MultipleDynamicSegments
      w <- uses mlsMemory memAddrWidth
      reprConstraints w $
        case Elf.virtAddrMap contents ph of
          Nothing -> do
            addWarning OverlappingLoadableSegments
            pure Map.empty
          Just virtMap -> do
            let dynContents = sliceL (Elf.phdrFileRange dynPhdr) contents
            -- Find th dynamic section from the contents.
            dynSection <- runDynamic $
              Elf.dynamicEntries (Elf.headerData hdr) (Elf.headerClass hdr) virtMap dynContents
            let symtab = dynamicSymbolTable dynSection
            mRelBuffer  <- runDynamic $ Elf.dynRelBuffer  dynSection
            mRelaBuffer <- runDynamic $ Elf.dynRelaBuffer dynSection
            SomeRelocationResolver resolver <- getRelocationResolver hdr
            when (isJust mRelBuffer && isJust mRelaBuffer) $ do
              addWarning $ DynamicRelaAndRelPresent
            let dta = Elf.headerData hdr
            loadtimeRelocs <-
              relocMapFromRelAndRela dta resolver symtab mRelBuffer mRelaBuffer
            pltRelocs <-
              case Elf.dynPLTRel dynSection of
                Left e -> do
                  addWarning $ RelocationParseFailure (show e)
                  pure $! Map.empty
                Right Elf.PLTEmpty -> do
                  pure $! Map.empty
                Right (Elf.PLTRel entries) -> do
                  pure $! Map.fromList $ zipWith (relocFromRel (toEndianness dta) symtab resolver) [0..] entries
                Right (Elf.PLTRela entries) -> do
                  pure $! Map.fromList $ zipWith (relocFromRela symtab resolver) [0..] entries
            pure $ Map.union loadtimeRelocs pltRelocs

------------------------------------------------------------------------
-- Elf segment loading

reprConstraints :: AddrWidthRepr w
                -> ((Bits (ElfWordType w)
                    , Integral (Elf.ElfIntType w)
                    , Integral (ElfWordType w)
                    , Show (ElfWordType w)
                    , MemWidth w) => a)
                -> a
reprConstraints Addr32 x = x
reprConstraints Addr64 x = x

-- | This creates a memory segment.
memSegment :: forall m w
           .  (Monad m, MemWidth w)
           => Map (MemWord w) (RelocEntry m w)
              -- ^ Map from region offset to relocation entry for segment.
           -> RegionIndex
              -- ^ Index of base (0=absolute address)
           -> Integer
              -- ^ Offset to add to linktime address for this segment (defaults to 0)
           -> Maybe SegmentIndex
              -- ^ Identifier for this segment in relocation if this is created from so/exe.
           -> MemWord w
              -- ^ Linktime address of segment.
           -> Perm.Flags
              -- ^ Flags if defined
           -> L.ByteString
           -- ^ File contents for segment.
           -> Int64
           -- ^ Expected size (must be positive)
           -> m (MemSegment w)
memSegment relocMap regionIndex regionOff msegIdx linkBaseOff flags bytes sz
      -- Return nothing if size is not positive
    | not (sz > 0) = error $ "Memory segments must have a positive size."
      -- Check for overflow in contents end
    | regionOff + toInteger linkBaseOff + toInteger sz > toInteger (maxBound :: MemWord w) =
      error "Contents two large for base."
    | otherwise = do
      contents <- byteSegments relocMap msegIdx linkBaseOff bytes sz
      let off = fromInteger regionOff + linkBaseOff
      pure $! mkMemSegment regionIndex off flags contents

-- | Load an elf file into memory.
insertElfSegment :: RegionIndex
                    -- ^ Region for elf segment
                 -> Integer
                    -- ^ Amount to add to linktime virtual address for thsi memory.
                 -> ElfFileSectionMap (ElfWordType w)
                 -> L.ByteString
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
      let dta = sliceL (Elf.phdrFileRange phdr) contents
      let sz = fromIntegral $ Elf.phdrMemSize phdr
      memSegment relocMap regIdx addrOff (Just segIdx) linkBaseOff flags dta sz
    loadMemSegment ("Segment " ++ show segIdx) seg
    let phdr_offset = Elf.fromFileOffset (Elf.phdrFileStart phdr)
    let phdr_end = phdr_offset + Elf.phdrFileSize phdr
    -- Add segment index to address mapping to memory object.
    mlsMemory %= memBindSegmentIndex segIdx seg
    -- Iterative through sections
    let l = IMap.toList $ IMap.intersecting shdrMap (IntervalCO phdr_offset phdr_end)
    forM_ l $ \(i, sec) -> do
      case i of
        IntervalCO shdr_start _ -> do
          let elfIdx = ElfSectionIndex (elfSectionIndex sec)
          when (phdr_offset > shdr_start) $ do
            error "Found section header that overlaps with program header."
          let sec_offset = fromIntegral $ shdr_start - phdr_offset
          let Just addr = resolveSegmentOff seg sec_offset
          mlsMemory   %= memBindSectionIndex (fromElfSectionIndex elfIdx) addr
          mlsIndexMap %= Map.insert elfIdx (addr, sec)
        _ -> error "Unexpected shdr interval"

-- | Load an elf file into memory by parsing segments.
memoryForElfSegments
  :: forall w
  .  RegionIndex
     -- ^ This is used as the base address to load Elf segments at (the virtual
     -- address is treated as relative to this.
  -> Integer
     -- ^ This is used as the base address to load Elf segments at (the virtual
     -- address is treated as relative to this.
  -> Elf  w
  -> MemLoader w ()
memoryForElfSegments regIndex addrOff e = do
  let l = elfLayout e
  let hdr = Elf.elfLayoutHeader l
  let w = elfAddrWidth (elfClass e)
  reprConstraints w $ do
    let ph  = Elf.allPhdrs l
    let contents = elfLayoutBytes l
    -- Create relocation map
    relocMap <- dynamicRelocationMap hdr ph contents

    let intervals :: ElfFileSectionMap (ElfWordType w)
        intervals = IMap.fromList
          [ (IntervalCO start end, sec)
          | shdr <- Map.elems (l ^. Elf.shdrs)
          , let start = shdr^._3
          , let sec = shdr^._1
          , let end = start + elfSectionFileSize sec
          ]
    mapM_ (insertElfSegment regIndex addrOff intervals contents relocMap)
          (filter (\p -> Elf.phdrSegmentType p == Elf.PT_LOAD) ph)

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
  [ (,) ".text"   True
  , (,) ".eh_frame" True
  , (,) ".data"   True
  , (,) ".bss"    False
  , (,) ".rodata" True
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
     ]

-- | Map from section names to information about them.
type SectionNameMap w =  Map SectionName [ElfSection (ElfWordType w)]

findSection :: SectionNameMap w
            -> SectionName
            -> MemLoader w (Maybe (ElfSection (ElfWordType w)))
findSection sectionMap nm =
  case Map.lookup nm sectionMap of
    Nothing -> pure Nothing
    Just [] -> pure Nothing
    Just (sec:rest) -> do
      when (not (null rest)) $ do
        addWarning $ MultipleSectionsWithName nm
      pure (Just sec)

-- | Add a section to the current memory
insertAllocatedSection :: Elf.ElfHeader w
                       -> SymbolTable
                       -> SectionNameMap w
                       -> RegionIndex
                          -- ^ Region for section (should be unique)
                       -> SectionName
                          -- ^ Name of section
                       -> MemLoader w ()
insertAllocatedSection hdr symtab sectionMap regIdx nm = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
   msec <- findSection sectionMap nm
   case msec of
    Nothing -> pure ()
    Just sec -> do
      mRelBuffer <- fmap (fmap (L.fromStrict . elfSectionData)) $
        findSection sectionMap (".rel" <> nm)
      mRelaBuffer <- fmap (fmap (L.fromStrict . elfSectionData)) $
        findSection sectionMap (".rela" <> nm)
      -- Build relocation map
      -- Get size of section
      let secSize = Elf.elfSectionSize sec
      -- Check if we should load section
      when (not (elfSectionFlags sec `Elf.hasPermissions` Elf.shf_alloc)) $ do
        addWarning $ SectionNotAlloc nm
      when (secSize > 0) $ do
        -- Get base address
        let base = elfSectionAddr sec
        -- Get section flags
        let flags = flagsForSectionFlags (elfSectionFlags sec)
        -- Get bytes as a lazy bytesize
        let bytes = L.fromStrict (elfSectionData sec)
        -- Create memory segment
        SomeRelocationResolver resolver <- getRelocationResolver hdr
        when (isJust mRelBuffer && isJust mRelaBuffer) $ do
          addWarning $ SectionRelaAndRelPresent nm
        relocMap <-
          relocMapFromRelAndRela (Elf.headerData hdr) resolver symtab mRelBuffer mRelaBuffer
        seg <-
          memSegment relocMap regIdx 0 Nothing (fromIntegral base) flags bytes (fromIntegral secSize)
        -- Load memory segment.
        loadMemSegment ("Section " ++ BSC.unpack (elfSectionName sec)) seg
        -- Add entry to map elf section index to start in segment.
        let elfIdx = ElfSectionIndex (elfSectionIndex sec)
        let Just addr = resolveSegmentOff seg 0
        mlsMemory   %= memBindSectionIndex (fromElfSectionIndex elfIdx) addr
        mlsIndexMap %= Map.insert elfIdx (addr, sec)

-- | Load allocated Elf sections into memory.
--
-- This is only used for object files.
memoryForElfSections :: forall w
                     .  Elf w
                     -> MemLoader w ()
memoryForElfSections e = do
  let hdr = Elf.elfHeader e
  -- Create map from section name to sections with that name.
  let sectionMap :: SectionNameMap w
      sectionMap = foldlOf elfSections insSec Map.empty e
        where insSec m sec = Map.insertWith (\new old -> old ++ new) (elfSectionName sec) [sec] m

  -- Parse Elf symbol table
  symtab <-
    case Elf.elfSymtab e of
      [] ->
        pure $ noSymTab
      elfSymTab:_rest -> do
        let entries = Elf.elfSymbolTableEntries elfSymTab
        --      let lclCnt = fromIntegral $ Elf.elfSymbolTableLocalEntries elfSymTab
        -- Create an unversioned symbol from symbol table.
        pure (staticSymTab entries)

  -- Insert sections
  forM_ (zip [1..] allocatedSectionInfo) $ \(idx, (nm,_)) -> do
    insertAllocatedSection hdr symtab sectionMap idx nm
  -- TODO: Figure out what to do about .tdata and .tbss
  -- Check for other section names that we do not support."
  let unsupportedKeys = Map.keysSet sectionMap `Set.difference ` allowedSectionNames
  forM_ unsupportedKeys $ \k -> do
    addWarning $ UnsupportedSection k

------------------------------------------------------------------------
-- High level loading

adjustedLoadRegionIndex :: Elf w -> LoadOptions -> RegionIndex
adjustedLoadRegionIndex e loadOpt =
  case loadRegionIndex loadOpt of
    Just idx -> idx
    Nothing ->
      case Elf.elfType e of
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

memoryForElf' :: LoadOptions
              -> Elf w
              -> Either String ( Memory w
                               , SectionIndexMap w
                               , [MemLoadWarning]
                               )
memoryForElf' opt e = reprConstraints (elfAddrWidth (elfClass e)) $ do
  let end = toEndianness (Elf.elfData e)
  runMemLoader end (emptyMemory (elfAddrWidth (elfClass e))) $
    case Elf.elfType e of
      -- We load object files by section
      Elf.ET_REL ->
        memoryForElfSections e
      -- Other files are loaded by segment.
      _ -> do
        let regIdx = adjustedLoadRegionIndex e opt
        let addrOff = loadRegionBaseOffset opt
        memoryForElfSegments regIdx addrOff e

-- | Load allocated Elf sections into memory.
--
-- Normally, Elf uses segments for loading, but the section
-- information tends to be more precise.
memoryForElf :: LoadOptions
             -> Elf w
             -> Either String ( Memory w
                              , [MemSymbol w] -- Function symbols
                              , [MemLoadWarning]
                              , [SymbolResolutionError]
                              )
memoryForElf opt e = do
  (mem, secMap, warnings) <- memoryForElf' opt e
  let (symErrs, funcSymbols) = resolveElfFuncSymbols mem secMap e
  pure (mem, funcSymbols, warnings, symErrs)

-- | Load allocated Elf sections into memory.
--
-- Normally, Elf uses segments for loading, but the segment
-- information tends to be more precise.
memoryForElfAllSymbols :: LoadOptions
                       -> Elf w
                       -> Either String ( Memory w
                              , [MemSymbol w] -- Function symbols
                              , [MemLoadWarning]
                              , [SymbolResolutionError]
                              )
memoryForElfAllSymbols opt e = do
  (mem, secMap, warnings) <- memoryForElf' opt e
  let (symErrs, funcSymbols) = resolveElfFuncSymbolsAny mem secMap e
  pure (mem, funcSymbols, warnings, symErrs)

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
resolveElfSymbol :: Memory w -- ^ Memory object from Elf file.
                 -> SectionIndexMap w -- ^ Section index mp from memory
                 -> Int -- ^ Index of symbol
                 -> ElfSymbolTableEntry (ElfWordType w)
                 -> Maybe (Either SymbolResolutionError (MemSymbol w))
resolveElfSymbol mem secMap idx ste
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
  | otherwise = reprConstraints (memAddrWidth mem) $ do
      let val = Elf.steValue ste
      case Map.lookup (Elf.steIndex ste) secMap of
        Just (base,sec)
          | elfSectionAddr sec <= val && val < elfSectionAddr sec + Elf.elfSectionSize sec
          , off <- toInteger val - toInteger (elfSectionAddr sec)
          , Just addr <- incSegmentOff base off -> Just $
              Right $ MemSymbol { memSymbolName = Elf.steName ste
                                , memSymbolStart = addr
                                , memSymbolSize = fromIntegral (Elf.steSize ste)
                                }
        _ -> Just $ Left $ CouldNotResolveAddr (Elf.steName ste)

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

ofResolvedSymbol :: Maybe (Either SymbolResolutionError (MemSymbol w))
                 -> ResolvedSymbols w
ofResolvedSymbol Nothing = mempty
ofResolvedSymbol (Just (Left e)) = resolutionError e
ofResolvedSymbol (Just (Right s)) = resolvedSymbol s

-- | Return true if section has the given name.
hasSectionName :: ElfSection w -> BS.ByteString -> Bool
hasSectionName section name = elfSectionName section == name

-- | Return true if section has the given name.
hasSectionIndex :: ElfSection w -> Word32 -> Bool
hasSectionIndex section idx = fromIntegral (elfSectionIndex section) == idx

-- | Resolve symbol table entries defined in this Elf file to
-- a mem symbol
--
-- It takes the memory constructed from the Elf file, the section
-- index map, and the elf file.  It returns errors from resolve symbols,
-- and a map from segment offsets to bytestring.
resolveElfFuncSymbols'
  :: forall w
  .  Memory w
  -> SectionIndexMap w
  -> (ElfSymbolTableEntry (ElfWordType w) -> Bool)
     -- ^ Filter on symbol table entries
  -> Elf w
  -> ([SymbolResolutionError], [MemSymbol w])
resolveElfFuncSymbols' mem secMap p e =
  let l = Elf.elfSymtab e

      staticEntries :: [(Int, ElfSymbolTableEntry (ElfWordType w))]
      staticEntries = concatMap (\tbl -> zip [0..] (V.toList (Elf.elfSymbolTableEntries tbl))) l

      cl = elfClass e
      dta = Elf.elfData e

      sections = e^..elfSections

      sectionFn idx =
        case filter (`hasSectionIndex` idx) sections of
          [s] -> Just s
          _ -> Nothing

      -- Get dynamic entries
      dynamicEntries :: [(Int, ElfSymbolTableEntry (ElfWordType w))]
      dynamicEntries
        | [symtab] <- filter (`hasSectionName` ".dynsym") sections
        , Right entries <- Elf.getSymbolTableEntries cl dta sectionFn symtab =
            zip [0..] entries
        | otherwise = []

      allEntries :: [(Int, ElfSymbolTableEntry (ElfWordType w))]
      allEntries = staticEntries ++ dynamicEntries

      multError =
        if length (Elf.elfSymtab e) > 1 then
          resolutionError MultipleSymbolTables
        else
          mempty
      resolvedEntries
        = mconcat
        $ fmap (ofResolvedSymbol . uncurry (resolveElfSymbol mem secMap))
        $ filter (\(_,s) -> p s) allEntries
      r = multError <> resolvedEntries
   in (resolutionErrors r, Set.toList (resolvedSymbols r))

resolveElfFuncSymbols
  :: forall w
  .  Memory w
  -> SectionIndexMap w
  -> Elf w
  -> ([SymbolResolutionError], [MemSymbol w])
resolveElfFuncSymbols mem secMap e = resolveElfFuncSymbols' mem secMap isRelevant e
  where isRelevant ste = Elf.steType ste == Elf.STT_FUNC


-- | Resolve symbol table entries to the addresses in a memory.
--
-- It takes the memory constructed from the Elf file, the section
-- index map, and the symbol table entries.  It returns unresolvable
-- symbols and the map from segment offsets to bytestring.
resolveElfFuncSymbolsAny
  :: forall w
  .  Memory w
  -> SectionIndexMap w
  -> Elf w
  -> ([SymbolResolutionError], [MemSymbol w])
resolveElfFuncSymbolsAny mem secMap e = resolveElfFuncSymbols' mem secMap (\_ -> True) e

------------------------------------------------------------------------
-- resolveElfContents

-- | Return the segment offset of the elf file entry point or fail if undefined.
getElfEntry ::  LoadOptions -> Memory w -> Elf w -> ([String], Maybe (MemSegmentOff w))
getElfEntry loadOpts mem e =  addrWidthClass (memAddrWidth mem) $
 Elf.elfClassInstances (Elf.elfClass e) $ do
   let regIdx = adjustedLoadRegionIndex e loadOpts
   let adjAddr = loadRegionBaseOffset loadOpts + toInteger (Elf.elfEntry e)
   case resolveRegionOff mem regIdx (fromInteger adjAddr) of
     Nothing ->
       ( ["Could not resolve entry point: " ++ showHex (Elf.elfEntry e) ""]
       , Nothing
       )
     Just v  -> ([], Just v)

-- | This interprets the Elf file to construct the initial memory,
-- entry points, and functions symbols.
--
-- If it encounters a fatal error it returns the error message in the left value,
-- and otherwise it returns the information interred as a 4-tuple.
resolveElfContents :: LoadOptions
                        -- ^ Options for loading contents
                     -> Elf w -- ^ Elf file to create memory
                     -> Either String
                           ( [String] -- Warnings
                           , Memory w -- Initial memory
                           , Maybe (MemSegmentOff w) -- Entry point(s)
                           , [MemSymbol w] -- Function symbols
                           )
resolveElfContents loadOpts e =
  case Elf.elfType e of
    Elf.ET_REL -> do
      (mem, funcSymbols, warnings, symErrs) <- memoryForElf loadOpts e
      pure (fmap show warnings ++ fmap show symErrs, mem, Nothing, funcSymbols)
    Elf.ET_EXEC -> do
      (mem, funcSymbols, warnings, symErrs) <- memoryForElf loadOpts e
      let (entryWarn, mentry) = getElfEntry loadOpts mem e
      Right (fmap show warnings ++ fmap show symErrs ++ entryWarn, mem, mentry, funcSymbols)
    Elf.ET_DYN -> do
      -- This is a shared library or position-independent executable.
      (mem, funcSymbols, warnings, symErrs) <- memoryForElf loadOpts e
      let (entryWarn, mentry) = getElfEntry loadOpts mem e
      pure (fmap show warnings ++ fmap show symErrs ++ entryWarn, mem, mentry, funcSymbols)
    Elf.ET_CORE ->
      Left  "Reopt does not support loading core files."
    tp ->
      Left $ "Reopt does not support loading elf files with type " ++ show tp ++ "."
