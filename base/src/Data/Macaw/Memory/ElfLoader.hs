{-|
Copyright) Galois Inc, 2016
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
module Data.Macaw.Memory.ElfLoader
  ( SectionIndexMap
  , memoryForElf
  , MemLoadWarning
  , resolveElfFuncSymbols
  , resolveElfFuncSymbolsAny
  , resolveElfContents
  , elfAddrWidth
  , module Data.Macaw.Memory.LoadCommon
  ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as L
import           Data.Either
import           Data.ElfEdit
  ( ElfIntType
  , ElfWordType

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

  , elfSegmentIndex
  , elfSegmentVirtAddr
  , ElfSegmentFlags
  , elfSegmentFlags
  , elfLayoutBytes

  , ElfSymbolTableEntry
  )
import qualified Data.ElfEdit as Elf
import           Data.Foldable
import           Data.IntervalMap.Strict (Interval(..), IntervalMap)
import qualified Data.IntervalMap.Strict as IMap
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Monoid
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import           Numeric (showHex)

import           Data.Macaw.Memory
import           Data.Macaw.Memory.LoadCommon
import qualified Data.Macaw.Memory.Permissions as Perm

-- | Return a subbrange of a bytestring.
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
-- RegionAdjust

-- | This captures how to translate addresses in the Elf file to
-- regions in the memory object.
data RegionAdjust
  = RegionAdjust { regionIndex :: !RegionIndex
                   -- ^ Region index for new segments
                 , regionOffset :: !Integer
                   -- ^ Offset from region to automatically add to
                   -- segment/sections during loading.
                 }

------------------------------------------------------------------------
-- MemLoader

type SectionName = B.ByteString
type SymbolName = B.ByteString

data MemLoadWarning
  = SectionNotAlloc !SectionName
  | MultipleSectionsWithName !SectionName
  | MultipleDynamicSegments
  | OverlappingLoadableSegments
  | RelocationParseFailure !String
  | UnsupportedSection !SectionName
  | UnknownDefinedSymbolBinding   !SymbolName Elf.ElfSymbolBinding
  | UnknownUndefinedSymbolBinding !SymbolName Elf.ElfSymbolBinding
  | UnsupportedProcessorSpecificSymbolIndex !SymbolName !ElfSectionIndex
  | IgnoreRelocation !RelocationError

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
  show (UnsupportedSection nm) =
    "Do not support section " ++ BSC.unpack nm
  show (UnknownDefinedSymbolBinding nm bnd) =
    "Unsupported binding " ++ show bnd ++ " for defined " ++ ppSymbol nm
    ++ "; Treating as a strong symbol."
  show (UnknownUndefinedSymbolBinding nm bnd) =
    "Unsupported binding " ++ show bnd ++ " for undefined " ++ ppSymbol nm
    ++ "; Treating as a required symbol."
  show (UnsupportedProcessorSpecificSymbolIndex nm idx) =
    "Could not resolve symbol index " ++ show idx ++ " for symbol " ++ BSC.unpack nm ++ "."
  show (IgnoreRelocation err) =
    "Ignoring relocation: " ++ show err

data MemLoaderState w = MLS { _mlsMemory :: !(Memory w)
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

data RelocationError
   = RelocationZeroSymbol
     -- ^ A relocation refers to the symbol index 0.
   | RelocationNonZeroAddend
     -- ^ A relocation entry had a non-zero addend.
   | RelocationBadSymbolIndex !Int
     -- ^ A relocation entry referenced a bad symbol index.
   | RelocationUnsupportedType !String
     -- ^ We do not support relocations with this architecture.

instance Show RelocationError where
  show RelocationZeroSymbol =
    "A relocation entry referred to invalid 0 symbol index."
  show RelocationNonZeroAddend =
    "Binary analysis framework does not yet support non-zero addend."
  show (RelocationBadSymbolIndex idx) =
    "A relocation entry referred to invalid symbol index " ++ show idx ++ "."
  show (RelocationUnsupportedType tp) =
    "Do not yet support relocation type " ++ tp ++ "."

data LoadError w
   = LoadInsertError !String !(InsertError w)
     -- ^ Error occurred in inserting a segment into memory.
   | RelocationDuplicateOffsets !(MemWord w)
     -- ^ Multiple relocations referenced the same offset.
   | UnsupportedArchitecture !String
     -- ^ Do not support relocations on given architecture.
   | FormatDynamicError !Elf.DynamicError
     -- ^ An error occured in parsing the dynamic segment.

instance MemWidth w => Show (LoadError w) where
  show (LoadInsertError nm (OverlapSegment _ old)) =
    nm ++ " overlaps with memory segment: " ++ show (segmentOffset old)
  show (UnsupportedArchitecture arch) =
    "Dynamic libraries are not supported on " ++ show arch ++ "."
  show (FormatDynamicError e) =
    "Elf parsing error: " ++ show e
  show (RelocationDuplicateOffsets o) =
    "Multiple relocations at offset " ++ show o ++ "."

runMemLoader :: Memory  w -> MemLoader w () -> Either String (SectionIndexMap w, Memory w, [MemLoadWarning])
runMemLoader mem m =
   let s = MLS { _mlsMemory = mem
               , _mlsIndexMap = Map.empty
               , mlsWarnings = []
               }
    in case runExcept $ execStateT m s of
         Left e -> Left $ addrWidthClass (memAddrWidth mem) (show e)
         Right mls -> Right (mls^.mlsIndexMap, mls^.mlsMemory, reverse (mlsWarnings mls))

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
-- Symbol information.

------------------------------------------------------------------------
-- RelocMap

-- | Information about a symbol after it has been resolved by an
-- architecture specific function.
data ResolvedRelocationTarget
   = TargetSymbol !SymbolRef
   | TargetCopy
     -- ^ This denotes that the symbol should be copied into fresh
     -- space in the application's BSS section.
     --
     -- Note that we currently ignore these symbols, and
   | TargetError !RelocationError
     -- ^ Indicates an error occured when resolving a relocation target.

-- | Map from symbol indices to the associated resolved symbol.
--
-- This drops the first symbol in Elf since that refers to no symbol
newtype SymbolVector = SymbolVector (V.Vector SymbolRef)

-- | A function that resolves the architecture-specific relocation-type
-- into a symbol reference.  The input
type RelocationResolver tp
  = SymbolVector
  -> Elf.RelaEntry tp
  -> ResolvedRelocationTarget

-- | Attempts to resolve a relocation entry into a specific target.
resolveSymbol  :: ( Eq (ElfIntType (Elf.RelocationWidth tp))
                  , Num (ElfIntType (Elf.RelocationWidth tp))
                  )
               => SymbolVector
                  -- ^ A vector mapping symbol indices to the
                  -- associated symbol information.
               -> Elf.RelaEntry tp
                  -- ^ A relocation entry
               -> ResolvedRelocationTarget
resolveSymbol (SymbolVector symtab) rel
  | Elf.r_addend rel /= 0 =
      TargetError $ RelocationNonZeroAddend
  | Elf.r_sym rel == 0 =
      TargetError $ RelocationZeroSymbol
  | otherwise =
      case symtab V.!? fromIntegral (Elf.r_sym rel - 1) of
        Nothing -> TargetError $ RelocationBadSymbolIndex $ fromIntegral (Elf.r_sym rel)
        Just sym -> TargetSymbol sym

-- | Attempt to resolve an X86_64 specific symbol.
relaTargetX86_64 :: RelocationResolver Elf.X86_64_RelocationType
relaTargetX86_64 symtab rel =
  case Elf.r_type rel of
    Elf.R_X86_64_GLOB_DAT  -> resolveSymbol symtab rel
    Elf.R_X86_64_COPY      -> TargetCopy
    Elf.R_X86_64_JUMP_SLOT -> resolveSymbol symtab rel
    tp -> TargetError (RelocationUnsupportedType (show tp))

-- | Attempt to resolve an ARM specific symbol.
relaTargetARM :: RelocationResolver Elf.ARM_RelocationType
relaTargetARM symtab rel =
  case Elf.r_type rel of
    Elf.R_ARM_GLOB_DAT -> resolveSymbol symtab rel
    Elf.R_ARM_COPY -> TargetCopy
    Elf.R_ARM_JUMP_SLOT -> resolveSymbol symtab rel
    tp -> TargetError (RelocationUnsupportedType (show tp))

-- | Creates a relocation map from the contents of a dynamic section.
withRelocationResolver
  :: forall w a
  .  Elf.ElfHeader w
  -> (forall tp
      . (w ~ Elf.RelocationWidth tp, Elf.IsRelocationType tp)
      => RelocationResolver tp
      -> MemLoader w a)
  -> MemLoader w a
withRelocationResolver hdr f =
  case (Elf.headerClass hdr, Elf.headerMachine hdr) of
    (Elf.ELFCLASS64, Elf.EM_X86_64) -> f relaTargetX86_64
    (Elf.ELFCLASS32, Elf.EM_ARM)    -> f relaTargetARM
    (_,mach) -> throwError $ UnsupportedArchitecture (show mach)

-- | Creates a map that forwards addresses to be relocated to their appropriate target.
addRelocEntry :: ( w ~ Elf.RelocationWidth tp
                 , MemWidth w
                 , Integral (Elf.RelocationWord tp)
                 )
              => RelocationResolver tp
              -> SymbolVector
              -> RelocMap (MemWord w)
              -> Elf.RelaEntry tp
              -> MemLoader w (RelocMap (MemWord w))
addRelocEntry relaTarget symtab relocMap rel =
  case relaTarget symtab rel of
    TargetSymbol tgt -> do
      let off = memWord (fromIntegral (Elf.r_offset rel))
      let (prev, newMap) = Map.insertLookupWithKey (\_ _n o -> o) off tgt relocMap
      case prev of
        Nothing -> pure ()
        Just _ -> throwError $ RelocationDuplicateOffsets off
      pure newMap
    TargetCopy -> pure relocMap
    TargetError e -> do
      addWarning (IgnoreRelocation e)
      pure relocMap

-- | This checks a computation that returns a dynamic error or succeeds.
runDynamic :: Either Elf.DynamicError a -> MemLoader w a
runDynamic (Left e) = throwError (FormatDynamicError e)
runDynamic (Right r) = pure r

mkRelocMap :: Elf.ElfHeader w
              -- ^ format for Elf file
           -> SymbolVector
              -- ^ Map from symbol indices to associated symbol
           -> L.ByteString
              -- ^ Buffer containing relocation entries in Rela format
           -> MemLoader w (RelocMap (MemWord w))
mkRelocMap hdr symtab relaBuffer = do
 w <- uses mlsMemory memAddrWidth
 reprConstraints w $ do
  withRelocationResolver hdr $ \resolver -> do
   let dta = Elf.headerData hdr
   case Elf.elfRelaEntries dta relaBuffer of
    Left msg -> do
      addWarning (RelocationParseFailure msg)
      pure Map.empty
    Right relocs -> do
      -- Create the relocation map using the above information
      foldlM (addRelocEntry resolver symtab) Map.empty relocs


resolvedDefinedSymbolPrec :: SymbolName -> Elf.ElfSymbolBinding -> MemLoader w SymbolPrecedence
resolvedDefinedSymbolPrec _ Elf.STB_LOCAL =
  pure $ SymbolLocal
resolvedDefinedSymbolPrec _ Elf.STB_WEAK =
  pure $ SymbolWeak
resolvedDefinedSymbolPrec _ Elf.STB_GLOBAL =
  pure $ SymbolStrong
resolvedDefinedSymbolPrec nm bnd = do
  addWarning $ UnknownDefinedSymbolBinding nm bnd
  pure $ SymbolStrong

-- | Create a symbol ref from Elf versioned symbol from a shared
-- object or executable.
mkSymbolRef :: ElfSymbolTableEntry wtp
            -> SymbolVersion
            -> MemLoader w SymbolRef
mkSymbolRef sym ver = do
  let nm = Elf.steName sym
  tp <-
    case Elf.steIndex sym of

      Elf.SHN_UNDEF -> do
        req <-
          case Elf.steBind sym of
            Elf.STB_WEAK -> do
              pure $ SymbolOptional
            Elf.STB_GLOBAL -> do
              pure $ SymbolRequired
            bnd -> do
              addWarning $ UnknownUndefinedSymbolBinding nm bnd
              pure $ SymbolRequired
        pure $! UndefinedSymbol req
      Elf.SHN_ABS -> do
        DefinedSymbol <$> resolvedDefinedSymbolPrec nm (Elf.steBind sym)
      Elf.SHN_COMMON -> do
        DefinedSymbol <$> resolvedDefinedSymbolPrec nm (Elf.steBind sym)
      idx | idx < Elf.SHN_LOPROC -> do
        DefinedSymbol <$> resolvedDefinedSymbolPrec nm (Elf.steBind sym)
      idx -> do
        addWarning $ UnsupportedProcessorSpecificSymbolIndex nm idx
        pure $ UndefinedSymbol SymbolRequired
  pure $
    SymbolRef { symbolName = Elf.steName sym
              , symbolVersion = ver
              , symbolType = tp
              }

-- | Create a symbol ref from Elf versioned symbol from a shared
-- object or executable.
mkDynamicSymbolRef :: Elf.VersionedSymbol tp
                   -> MemLoader w SymbolRef
mkDynamicSymbolRef (sym, mverId) = do
  let ver = case mverId of
              Elf.VersionLocal -> UnversionedSymbol
              Elf.VersionGlobal -> UnversionedSymbol
              Elf.VersionSpecific elfVer -> VersionedSymbol (Elf.verFile elfVer) (Elf.verName elfVer)
  mkSymbolRef sym ver

-- | Create a relocation map from the dynamic loader information.
dynamicRelocationMap :: Elf.ElfHeader w
                     -> [Elf.Phdr w]
                     -> L.ByteString
                     -> MemLoader w (RelocMap (MemWord w))
dynamicRelocationMap hdr ph contents = do
  case filter (Elf.hasSegmentType Elf.PT_DYNAMIC . Elf.phdrSegment) ph of
    [] -> pure Map.empty
    dynPhdr:dynRest -> do
      when (not (null dynRest)) $ do
        addWarning $ MultipleDynamicSegments
      w <- uses mlsMemory memAddrWidth
      reprConstraints w $ do
        case Elf.virtAddrMap contents ph of
          Nothing -> do
            addWarning OverlappingLoadableSegments
            pure Map.empty
          Just virtMap -> do
            let dynContents = sliceL (Elf.phdrFileRange dynPhdr) contents
            -- Find th dynamic section from the contents.
            dynSection <- runDynamic $
              Elf.dynamicEntries (Elf.headerData hdr) (Elf.headerClass hdr) virtMap dynContents
            symentries <- runDynamic (Elf.dynSymTable dynSection)
            symtab <-
              SymbolVector <$> traverse mkDynamicSymbolRef (V.drop 1 symentries)
            maybeRelaBuf <- runDynamic $ Elf.dynRelaBuffer dynSection
            case maybeRelaBuf of
              Nothing -> pure Map.empty
              Just relaBuf -> mkRelocMap hdr symtab relaBuf

------------------------------------------------------------------------
-- Elf segment loading

reprConstraints :: AddrWidthRepr w
                -> ((Bits (ElfWordType w), Integral (ElfWordType w), Show (ElfWordType w), MemWidth w) => a)
                -> a
reprConstraints Addr32 x = x
reprConstraints Addr64 x = x

-- | Return a memory segment for elf segment if it loadable.
memSegmentForElfSegment :: (MemWidth w, Integral (ElfWordType w))
                        => RegionAdjust -- ^ Index for segment
                        -> L.ByteString
                           -- ^ Complete contents of Elf file.
                        -> RelocMap (MemWord w)
                           -- ^ Relocation map
                        -> Elf.Phdr w
                           -- ^ Program header entry
                        -> MemSegment w
memSegmentForElfSegment regAdj contents relocMap phdr =
    memSegment (regionIndex regAdj) relocMap (fromInteger base) flags dta sz
  where seg = Elf.phdrSegment phdr
        dta = sliceL (Elf.phdrFileRange phdr) contents
        sz = fromIntegral $ Elf.phdrMemSize phdr
        base = regionOffset regAdj + toInteger (elfSegmentVirtAddr seg)
        flags = flagsForSegmentFlags (elfSegmentFlags seg)

-- | Load an elf file into memory.
insertElfSegment :: RegionAdjust
                    -- ^ Where to load region
                 -> ElfFileSectionMap (ElfWordType w)
                 -> L.ByteString
                 -> RelocMap (MemWord w)
                    -- ^ Relocations to apply in loading section.
                 -> Elf.Phdr w
                 -> MemLoader w ()
insertElfSegment regAdj shdrMap contents relocMap phdr = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
  when (Elf.phdrMemSize phdr > 0) $ do
    let seg = memSegmentForElfSegment regAdj contents relocMap phdr
    let seg_idx = elfSegmentIndex (Elf.phdrSegment phdr)
    loadMemSegment ("Segment " ++ show seg_idx) seg
    let phdr_offset = Elf.fromFileOffset (Elf.phdrFileStart phdr)
    let phdr_end = phdr_offset + Elf.phdrFileSize phdr
    let l = IMap.toList $ IMap.intersecting shdrMap (IntervalCO phdr_offset phdr_end)
    forM_ l $ \(i, sec) -> do
      case i of
        IntervalCO shdr_start _ -> do
          let elfIdx = ElfSectionIndex (elfSectionIndex sec)
          when (phdr_offset > shdr_start) $ do
            fail $ "Found section header that overlaps with program header."
          let sec_offset = fromIntegral $ shdr_start - phdr_offset
          let Just addr = resolveSegmentOff seg sec_offset
          mlsIndexMap %= Map.insert elfIdx (addr, sec)
        _ -> fail "Unexpected shdr interval"

-- | Load an elf file into memory with the given options.
memoryForElfSegments
  :: forall w
  .  RegionAdjust
  -> Elf  w
  -> MemLoader w ()
memoryForElfSegments regAdj e = do
  let l = elfLayout e
  let hdr = Elf.elfLayoutHeader l
  let w = elfAddrWidth (elfClass e)
  reprConstraints w $ do
  let ph  = Elf.allPhdrs l
  let contents = elfLayoutBytes l
  -- Create relocation map
  relocMap <-
      dynamicRelocationMap hdr ph contents

  let intervals :: ElfFileSectionMap (ElfWordType w)
      intervals = IMap.fromList $
          [ (IntervalCO start end, sec)
          | shdr <- Map.elems (l ^. Elf.shdrs)
          , let start = shdr^._3
          , let sec = shdr^._1
          , let end = start + elfSectionFileSize sec
          ]
  mapM_ (insertElfSegment regAdj intervals contents relocMap)
        (filter (Elf.hasSegmentType Elf.PT_LOAD . Elf.phdrSegment) ph)

------------------------------------------------------------------------
-- Elf section loading

allowedSectionNames :: Set B.ByteString
allowedSectionNames = Set.fromList
  [ ""
  , ".text", ".rela.text"
  , ".data", ".rela.data"
  , ".bss"
  , ".tbss"
  , ".tdata", ".rela.tdata"
  , ".rodata", ".rela.rodata"
  , ".comment"
  , ".note.GNU-stack"
  , ".eh_frame", ".rela.eh_frame"
  , ".shstrtab"
  , ".symtab"
  , ".strtab"
  ]

-- | Map from section names to information about them.
type SectionNameMap w =  Map SectionName [ElfSection (ElfWordType w)]

findSection :: SectionNameMap w -> SectionName -> MemLoader w (Maybe (ElfSection (ElfWordType w)))
findSection sectionMap nm =
  case Map.lookup nm sectionMap of
    Nothing -> pure Nothing
    Just [] -> pure Nothing
    Just (sec:rest) -> do
      when (not (null rest)) $ do
        addWarning $ MultipleSectionsWithName nm
      pure (Just sec)

insertAllocatedSection :: Elf.ElfHeader w
                       -> SymbolVector
                       -> SectionNameMap w
                       -> RegionIndex
                       -> SectionName
                       -> MemLoader w ()
insertAllocatedSection hdr symtab sectionMap regIdx nm = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
  msec <- findSection sectionMap nm
  case msec of
    Nothing -> pure ()
    Just sec -> do
      mRelocSec <- findSection sectionMap (".rela" <> nm)
      -- Build relocation map
      relocMap <-
        case mRelocSec of
          Nothing ->
            pure Map.empty
          Just relSec -> do
            let relaBuffer = L.fromStrict (elfSectionData relSec)
            mkRelocMap hdr symtab relaBuffer
      -- Get size of section
      let secSize = fromIntegral (Elf.elfSectionSize sec)
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
        let seg = memSegment regIdx relocMap (fromIntegral base) flags bytes secSize
        -- Load memory segment.
        loadMemSegment ("Section " ++ BSC.unpack (elfSectionName sec)) seg
        -- Add entry to map elf section index to start in segment.
        let elfIdx = ElfSectionIndex (elfSectionIndex sec)
        let Just addr = resolveSegmentOff seg 0
        mlsIndexMap %= Map.insert elfIdx (addr, sec)

-- | Create the symbol vector from
symtabSymbolVector :: forall w . Elf w -> MemLoader w SymbolVector
symtabSymbolVector e =
  case Elf.elfSymtab e of
    [] ->
      pure $ SymbolVector V.empty
    elfSymTab:_rest -> do
--      when (not (null rest)) $ addWarning $ MultipleSymbolTables
      let entries = Elf.elfSymbolTableEntries elfSymTab
--      let lclCnt = fromIntegral $ Elf.elfSymbolTableLocalEntries elfSymTab
      -- Create an unversioned symbol from symbol table.
      let mk :: ElfSymbolTableEntry wtp -> MemLoader w SymbolRef
          mk ent = mkSymbolRef ent ObjectSymbol
      SymbolVector <$> traverse mk (V.drop 1 entries)

-- | Load allocated Elf sections into memory.
--
-- Normally, Elf uses segments for loading, but the segment
-- information tends to be more precise.
memoryForElfSections :: forall w
                     .  Elf w
                     -> MemLoader w ()
memoryForElfSections e = do
  let hdr = Elf.elfHeader e
  -- Create map from section name to sections with that name.
  let sectionMap :: SectionNameMap w
      sectionMap = foldlOf elfSections insSec Map.empty e
        where insSec m sec = Map.insertWith (\new old -> old ++ new) (elfSectionName sec) [sec] m
  symtab <- symtabSymbolVector e
  insertAllocatedSection hdr symtab sectionMap 1 ".text"
  insertAllocatedSection hdr symtab sectionMap 2 ".data"
  insertAllocatedSection hdr symtab sectionMap 3 ".bss"
  insertAllocatedSection hdr symtab sectionMap 4 ".rodata"
  -- TODO: Figure out what to do about .tdata and .tbss
  -- Check for other section names that we do not support."
  let unsupportedKeys = Map.keysSet sectionMap `Set.difference ` allowedSectionNames
  forM_ unsupportedKeys $ \k -> do
    addWarning $ UnsupportedSection k

------------------------------------------------------------------------
-- High level loading

-- | Return true if Elf has a @PT_DYNAMIC@ segment (thus indicating it
-- is relocatable.
isRelocatable :: Elf w -> Bool
isRelocatable e = any (Elf.hasSegmentType Elf.PT_DYNAMIC) (Elf.elfSegments e)

adjustedLoadRegionIndex :: Elf w -> LoadOptions -> RegionIndex
adjustedLoadRegionIndex e loadOpt =
  case loadRegionIndex loadOpt of
    Just idx -> idx
    Nothing ->
      case Elf.elfType e of
        Elf.ET_REL -> 1
        Elf.ET_EXEC -> if isRelocatable e then 1 else 0
        Elf.ET_DYN -> 1
        _ -> 0

-- | Load allocated Elf sections into memory.
--
-- Normally, Elf uses segments for loading, but the segment
-- information tends to be more precise.
memoryForElf :: LoadOptions
             -> Elf w
             -> Either String (SectionIndexMap w, Memory w, [MemLoadWarning])
memoryForElf opt e = do
  runMemLoader (emptyMemory (elfAddrWidth (elfClass e))) $ do
    case Elf.elfType e of
      Elf.ET_REL ->
        memoryForElfSections e
      _ -> do
        let regAdj = RegionAdjust { regionIndex  = adjustedLoadRegionIndex e opt
                                  , regionOffset = loadRegionBaseOffset opt
                                  }
        memoryForElfSegments regAdj e

------------------------------------------------------------------------
-- Elf symbol utilities

-- | Error when resolving symbols.
data SymbolResolutionError
   = EmptySymbolName !Int !Elf.ElfSymbolType
     -- ^ Symbol names must be non-empty
   | CouldNotResolveAddr !BSC.ByteString
     -- ^ Symbol address could not be resolved.
   | MultipleSymbolTables
     -- ^ The elf file contained multiple symbol tables

instance Show SymbolResolutionError where
  show (EmptySymbolName idx tp ) = "Symbol Num " ++ show idx ++ " " ++ show tp ++ " has an empty name."
  show (CouldNotResolveAddr sym) = "Could not resolve address of " ++ BSC.unpack sym ++ "."
  show MultipleSymbolTables = "Elf contains multiple symbol tables."

-- | Find an absolute symbol, of any time, not just function.
resolveElfFuncSymbolAny ::
  Memory w -- ^ Memory object from Elf file.
                     -> SectionIndexMap w -- ^ Section index mp from memory
                     -> Int -- ^ Index of symbol
                     -> ElfSymbolTableEntry (ElfWordType w)
                     -> Maybe (Either SymbolResolutionError (MemSymbol w))
resolveElfFuncSymbolAny mem secMap idx ste

    -- Check symbol is defined
  | Elf.steIndex ste == Elf.SHN_UNDEF = Nothing
  -- Check symbol name is non-empty
  | Elf.steName ste == "" = Just $ Left $ EmptySymbolName idx (Elf.steType ste)
  -- Lookup absolute symbol
  | Elf.steIndex ste == Elf.SHN_ABS = reprConstraints (memAddrWidth mem) $ do
      let val = Elf.steValue ste
      case resolveAddr mem 0 (fromIntegral val) of
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
          , Just addr <- incSegmentOff base off -> do
              Just $ Right $ MemSymbol { memSymbolName = Elf.steName ste
                                       , memSymbolStart = addr
                                       , memSymbolSize = fromIntegral (Elf.steSize ste)
                                       }
        _ -> Just $ Left $ CouldNotResolveAddr (Elf.steName ste)




-- | This resolves an Elf symbol into a MemSymbol if it is likely a
-- pointer to a resolved function.
resolveElfFuncSymbol :: Memory w -- ^ Memory object from Elf file.
                     -> SectionIndexMap w -- ^ Section index mp from memory
                     -> Int -- ^ Index of symbol
                     -> ElfSymbolTableEntry (ElfWordType w)
                     -> Maybe (Either SymbolResolutionError (MemSymbol w))
resolveElfFuncSymbol mem secMap idx ste
  -- Check this is a defined function symbol
  -- Some NO_TYPE entries appear to correspond to functions, so we include those.
  | (Elf.steType ste `elem` [ Elf.STT_FUNC, Elf.STT_NOTYPE ]) == False =
    Nothing
    -- Check symbol is defined
  | Elf.steIndex ste == Elf.SHN_UNDEF = Nothing
  -- Check symbol name is non-empty
  | Elf.steName ste == "" = Just $ Left $ EmptySymbolName idx (Elf.steType ste)
  -- Lookup absolute symbol
  | Elf.steIndex ste == Elf.SHN_ABS = reprConstraints (memAddrWidth mem) $ do
      let val = Elf.steValue ste
      case resolveAddr mem 0 (fromIntegral val) of
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
          , Just addr <- incSegmentOff base off -> do
              Just $ Right $ MemSymbol { memSymbolName = Elf.steName ste
                                       , memSymbolStart = addr
                                       , memSymbolSize = fromIntegral (Elf.steSize ste)
                                       }
        _ -> Just $ Left $ CouldNotResolveAddr (Elf.steName ste)

-- | Resolve symbol table entries defined in this Elf file to
-- a mem symbol
--
-- It takes the memory constructed from the Elf file, the section
-- index map, and the symbol table entries.  It returns unresolvable
-- symbols and the map from segment offsets to bytestring.
resolveElfFuncSymbols
  :: forall w
  .  Memory w
  -> SectionIndexMap w
  -> Elf w
  -> ([SymbolResolutionError], [MemSymbol w])
resolveElfFuncSymbols mem secMap e =
  case Elf.elfSymtab e of
    [] -> ([], [])
    [tbl] ->
      let entries = V.toList (Elf.elfSymbolTableEntries tbl)
       in partitionEithers (mapMaybe (uncurry (resolveElfFuncSymbol mem secMap)) (zip [0..] entries))
    _ -> ([MultipleSymbolTables], [])


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
resolveElfFuncSymbolsAny mem secMap e =
  case Elf.elfSymtab e of
    [] -> ([], [])
    [tbl] ->
      let entries = V.toList (Elf.elfSymbolTableEntries tbl)
       in partitionEithers (mapMaybe (uncurry (resolveElfFuncSymbolAny mem secMap)) (zip [0..] entries))
    _ -> ([MultipleSymbolTables], [])



------------------------------------------------------------------------
-- resolveElfContents

-- | Return the segment offset of the elf file entry point or fail if undefined.
getElfEntry ::  LoadOptions -> Memory w -> Elf w -> ([String], Maybe (MemSegmentOff w))
getElfEntry loadOpts mem e =  addrWidthClass (memAddrWidth mem) $ do
 Elf.elfClassInstances (Elf.elfClass e) $ do
   let regIdx = adjustedLoadRegionIndex e loadOpts
   let adjAddr = loadRegionBaseOffset loadOpts + toInteger (Elf.elfEntry e)
   case resolveAddr mem regIdx (fromInteger adjAddr) of
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
resolveElfContents loadOpts e = do
  case Elf.elfType e of
    Elf.ET_REL -> do
      (secMap, mem, warnings) <- memoryForElf loadOpts e
      let (symErrs, funcSymbols) = resolveElfFuncSymbols mem secMap e
      pure (fmap show warnings ++ fmap show symErrs, mem, Nothing, funcSymbols)
    Elf.ET_EXEC -> do
      (secMap, mem, warnings) <- memoryForElf loadOpts e
      let (entryWarn, mentry) = getElfEntry loadOpts mem e
      let (symErrs, funcSymbols) = resolveElfFuncSymbols mem secMap e
      Right (fmap show warnings ++ entryWarn ++ fmap show symErrs, mem, mentry, funcSymbols)
    Elf.ET_DYN -> do
      (secMap, mem, warnings) <- memoryForElf loadOpts e
      let (entryWarn, mentry) = getElfEntry loadOpts mem e
      let (symErrs, funcSymbols) = resolveElfFuncSymbols mem secMap e
      pure (fmap show warnings ++ entryWarn ++ fmap show symErrs, mem, mentry, funcSymbols)
    Elf.ET_CORE -> do
      Left $ "Reopt does not support loading core files."
    tp -> do
      Left $ "Reopt does not support loading elf files with type " ++ show tp ++ "."
