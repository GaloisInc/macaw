{-|
Module      : Data.Macaw.Memory.ElfLoader
Copyright   : (c) Galois Inc, 2016
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
  , LoadStyle(..)
  , LoadOptions(..)
  , memoryForElf
    -- * High-level exports
  , readElf
  , loadExecutable
    -- * Symbol resolution utilities
  , resolveElfFuncSymbols
  , ppElfUnresolvedSymbols
  , elfAddrWidth
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
  ( SomeElf(..)
  , ElfIntType
  , ElfWordType
  , ElfGetResult(..)

  , Elf
  , elfSections
  , elfLayout

  , ElfClass(..)
  , elfClass
  , ElfMachine(..)
  , elfMachine
  , ElfData(..)

  , ElfParseError
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
  , elfLayoutData

  , ElfSymbolTableEntry
  )
import qualified Data.ElfEdit as Elf
import           Data.Foldable
import           Data.IntervalMap.Strict (Interval(..), IntervalMap)
import qualified Data.IntervalMap.Strict as IMap
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Some
import qualified Data.Vector as V
import           Numeric (showHex)
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.Memory
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
-- LoadOptions

-- | How to load Elf file.
data LoadStyle
   = LoadBySection
     -- ^ Load loadable sections in Elf file.
   | LoadBySegment
     -- ^ Load segments in Elf file.
  deriving (Eq)

data LoadOptions
   = LoadOptions { loadRegionIndex :: !RegionIndex
                   -- ^ Defines the "region" to load sections and segments into.
                   --
                   -- This should be 0 for static libraries since their addresses are
                   -- absolute.  It should likely be non-zero for shared library since their
                   -- addresses are relative.  Different shared libraries loaded into the
                   -- same memory should have different region indices.
                 , loadStyle :: !LoadStyle
                   -- ^ Controls whether to load by section or segment
                 , includeBSS :: !Bool
                   -- ^ Include data not backed by file when creating memory segments.
                 }

------------------------------------------------------------------------
-- MemSegment

-- | Return segments for data
byteSegments :: forall w
             .  MemWidth w
             => RelocMap (MemWord w)
             -> MemWord w -- ^ Base address for segment
             -> L.ByteString
             -> [SegmentRange w]
byteSegments m0 base0 contents0 = go base0 (Map.toList m) contents0
  where end = base0 + fromIntegral (L.length contents0)
        -- Get only those elements in m between [base0, end)
        m = Map.takeWhileAntitone (< end)
          $ Map.dropWhileAntitone (< base0) m0
        -- Get size of address
        ptrSize :: MemWord w
        ptrSize = fromIntegral (addrSize base0)
        -- Return segment range for contents.
        singleSegment :: L.ByteString -> [SegmentRange w]
        singleSegment contents | L.null contents = []
                               | otherwise = [ByteRegion (L.toStrict contents)]
        -- Create segments
        go :: MemWord w -> [(MemWord w, SymbolRef)] -> L.ByteString -> [SegmentRange w]
        go _ [] contents = singleSegment contents
        go base ((addr,tgt):rest) contents =
            preseg ++ [SymbolicRef tgt] ++ go (addr + ptrSize) rest post
          where off = addr - base
                preseg = singleSegment (L.take (fromIntegral off) contents)
                post   = L.drop (fromIntegral (off + ptrSize)) contents

-- | Return a memory segment for elf segment if it loadable.
memSegmentForElfSegment :: (MemWidth w, Integral (ElfWordType w))
                        => LoadOptions
                        -> L.ByteString
                           -- ^ Complete contents of Elf file.
                        -> RelocMap (MemWord w)
                           -- ^ Relocation map
                        -> Elf.Phdr w
                           -- ^ Program header entry
                        -> MemSegment w
memSegmentForElfSegment opt contents relocMap phdr = mseg
  where seg = Elf.phdrSegment phdr
        dta = sliceL (Elf.phdrFileRange phdr) contents
        sz = fromIntegral $ Elf.phdrMemSize phdr
        fixedData
          | L.length dta > sz = L.take sz dta
          | includeBSS opt = dta `mappend` L.replicate (sz - L.length dta) 0
          | otherwise = dta
        addr = fromIntegral $ elfSegmentVirtAddr seg
        flags = flagsForSegmentFlags (elfSegmentFlags seg)
        mseg = memSegment (loadRegionIndex opt) addr flags (byteSegments relocMap addr fixedData)

-- | Create memory segment from elf section.
memSegmentForElfSection :: (Integral v, Bits v, MemWidth w)
                        => RegionIndex
                        -> ElfSection v
                        -> MemSegment w
memSegmentForElfSection reg s = mseg
  where base = fromIntegral (elfSectionAddr s)
        flags = flagsForSectionFlags (elfSectionFlags s)
        bytes = elfSectionData s
        mseg = memSegment reg base flags [ByteRegion bytes]

------------------------------------------------------------------------
-- MemLoader

data MemLoaderState w = MLS { mlsOptions :: !LoadOptions
                              -- ^ All sections and segments should be loaded in this region.
                            , _mlsMemory :: !(Memory w)
                            , _mlsIndexMap :: !(SectionIndexMap w)
                            }

mlsMemory :: Simple Lens (MemLoaderState w) (Memory w)
mlsMemory = lens _mlsMemory (\s v -> s { _mlsMemory = v })

-- | Map from elf section indices to their offset and section
mlsIndexMap :: Simple Lens (MemLoaderState w) (SectionIndexMap w)
mlsIndexMap = lens _mlsIndexMap (\s v -> s { _mlsIndexMap = v })

memLoaderPair :: MemLoaderState w -> (SectionIndexMap w, Memory w)
memLoaderPair mls = (mls^.mlsIndexMap, mls^.mlsMemory)

type MemLoader w = StateT (MemLoaderState w) (Except String)

runMemLoader :: LoadOptions -> Memory  w -> MemLoader w () -> Either String (SectionIndexMap w, Memory w)
runMemLoader opt mem m = fmap memLoaderPair $ runExcept $ execStateT m s
   where s = MLS { mlsOptions = opt
                 , _mlsMemory = mem
                 , _mlsIndexMap = Map.empty
                 }


-- | This adds a Macaw mem segment to the memory
loadMemSegment :: MemWidth w => String -> MemSegment w -> MemLoader w ()
loadMemSegment nm seg =
  StateT $ \mls -> do
    case insertMemSegment seg (mls^.mlsMemory) of
      Left (OverlapSegment _ old) ->
        throwError $ nm ++ " overlaps with memory segment: " ++ show (segmentOffset old)
      Right mem' -> do
        pure ((), mls & mlsMemory .~ mem')

-- | Maps file offsets to the elf section
type ElfFileSectionMap v = IntervalMap v (ElfSection v)

------------------------------------------------------------------------
-- Symbol information.

-- | Ma an Elf version id to
mkSymbolVersion :: Elf.VersionId -> SymbolVersion
mkSymbolVersion ver = SymbolVersion { symbolVersionFile = Elf.verFile ver
                                    , symbolVersionName = Elf.verName ver
                                    }

mkSymbolRef :: Elf.VersionedSymbol tp -> SymbolRef
mkSymbolRef (sym, mverId) =
  SymbolRef { symbolName = Elf.steName sym
            , symbolVersion = mkSymbolVersion <$> mverId
            }

------------------------------------------------------------------------
-- RelocMap

-- | Maps symbols to their relocated target
type RelocMap w = Map w SymbolRef

checkZeroAddend :: ( Eq (ElfIntType (Elf.RelocationWidth tp))
                   , Num (ElfIntType (Elf.RelocationWidth tp))
                   )
                => Elf.RelaEntry tp
                -> Either String ()
checkZeroAddend rel =
  when (Elf.r_addend rel /= 0) $ Left "Cannot relocate symbols with non-zero addend."

relaSymbol  :: V.Vector v -> Elf.RelaEntry tp -> Either String v
relaSymbol symtab rel =
  case symtab V.!? fromIntegral (Elf.r_sym rel) of
    Nothing -> Left $ "Could not find symbol at index " ++ show (Elf.r_sym rel) ++ "."
    Just sym -> Right sym

-- | Creates a map that forwards addresses to be relocated to their appropriate target.
relaTarget :: V.Vector SymbolRef
           -> Elf.RelaEntry Elf.X86_64_RelocationType
           -> Either String (Maybe SymbolRef)
relaTarget symtab rel =
  case Elf.r_type rel of
    Elf.R_X86_64_GLOB_DAT -> do
      checkZeroAddend rel
      Just <$> relaSymbol symtab rel
    Elf.R_X86_64_COPY -> Right Nothing
    Elf.R_X86_64_JUMP_SLOT -> do
      checkZeroAddend rel
      Just <$> relaSymbol symtab rel
    tp -> Left $ "Do not yet support relocation type: " ++ show tp

-- | Creates a map that forwards addresses to be relocated to their appropriate target.
relocEntry :: V.Vector SymbolRef
           -> Elf.RelaEntry Elf.X86_64_RelocationType
           -> Either String (Maybe (MemWord 64, SymbolRef))
relocEntry symtab rel = fmap (fmap f) $ relaTarget symtab rel
  where f :: a -> (MemWord 64, a)
        f tgt = (memWord (Elf.r_offset rel), tgt)


-- Given a list returns a map mapping keys to their associated values, or
-- a key that appears in multiple elements.
mapFromListUnique :: Ord k => [(k,v)] -> Either k (Map k v)
mapFromListUnique = foldlM f Map.empty
  where f m (k,v) =
          case Map.lookup k m of
            Nothing -> Right $! Map.insert k v m
            Just _ -> Left k

-- | Creates a map that forwards addresses to be relocated to their appropriate target.
mkRelocMap :: V.Vector SymbolRef
           -> [Elf.RelaEntry Elf.X86_64_RelocationType]
           -> Either String (RelocMap (MemWord 64))
mkRelocMap symtab l = do
  mentries <- traverse (relocEntry symtab) l
  let errMsg w = show w ++ " appears in multiple relocations."
  case mapFromListUnique $ catMaybes mentries of
    Left dup -> Left (errMsg dup)
    Right v -> Right v

-- | Creates a relocation map from the contents of a dynamic section.
relocMapOfDynamic :: ElfData
                  -> ElfClass w
                  -> ElfMachine
                  -> Elf.VirtAddrMap w
                  -> L.ByteString -- ^ Contents of .dynamic section
                  -> MemLoader w (RelocMap (MemWord w))
relocMapOfDynamic d cl mach virtMap dynContents =
  case (cl, mach) of
    (Elf.ELFCLASS64, Elf.EM_X86_64) -> do
      dynSection <- either (throwError . show) pure $
        Elf.dynamicEntries d cl virtMap dynContents
      relocs <- either (throwError . show) pure $
        Elf.dynRelocations (dynSection :: Elf.DynamicSection Elf.X86_64_RelocationType)
      syms <- either (throwError . show) pure $
        Elf.dynSymTable dynSection
      either throwError pure $
        mkRelocMap (mkSymbolRef <$> syms) relocs
    _ -> throwError $ "Dynamic libraries are not supported on " ++ show mach ++ "."

------------------------------------------------------------------------
-- Elf segment loading

reprConstraints :: AddrWidthRepr w
                -> ((Bits (ElfWordType w), Integral (ElfWordType w), Show (ElfWordType w), MemWidth w) => a)
                -> a
reprConstraints Addr32 x = x
reprConstraints Addr64 x = x

-- | Load an elf file into memory.
insertElfSegment :: ElfFileSectionMap (ElfWordType w)
                 -> L.ByteString
                 -> RelocMap (MemWord w)
                    -- ^ Relocations to apply in loading section.
                 -> Elf.Phdr w
                 -> MemLoader w ()
insertElfSegment shdrMap contents relocMap phdr = do
  opt <- gets mlsOptions
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
  let seg = memSegmentForElfSegment opt  contents relocMap phdr
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
  .  Elf  w
  -> MemLoader w ()
memoryForElfSegments e = do
  let l = elfLayout e
  let w = elfAddrWidth (elfClass e)
  reprConstraints w $ do
  let d   = elfLayoutData l
  let ph  = Elf.allPhdrs l
  let contents = elfLayoutBytes l
  virtMap <- maybe (throwError "Overlapping loaded segments") pure $
    Elf.virtAddrMap contents ph
  relocMap <-
    case filter (Elf.hasSegmentType Elf.PT_DYNAMIC . Elf.phdrSegment) ph of
      [] -> pure Map.empty
      [dynPhdr] -> do
        let dynContents = sliceL (Elf.phdrFileRange dynPhdr) contents
        relocMapOfDynamic d (elfClass e) (elfMachine e) virtMap dynContents
      _ -> throwError "Multiple dynamic sections"

  let intervals :: ElfFileSectionMap (ElfWordType w)
      intervals = IMap.fromList $
          [ (IntervalCO start end, sec)
          | shdr <- Map.elems (l ^. Elf.shdrs)
          , let start = shdr^._3
          , let sec = shdr^._1
          , let end = start + elfSectionFileSize sec
          ]
  mapM_ (insertElfSegment intervals contents relocMap)
        (filter (Elf.hasSegmentType Elf.PT_LOAD . Elf.phdrSegment) ph)

------------------------------------------------------------------------
-- Elf section loading

-- | Load an elf file into memory.
insertElfSection :: ElfSection (ElfWordType w)
                 -> MemLoader w ()
insertElfSection sec = do
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
  -- Check if we should load section
  let doLoad = elfSectionFlags sec `Elf.hasPermissions` Elf.shf_alloc
            && elfSectionName sec /= ".eh_frame"
  when doLoad $ do
    regIdx <- gets $ loadRegionIndex . mlsOptions
    let seg = memSegmentForElfSection regIdx sec
    loadMemSegment ("Section " ++ BSC.unpack (elfSectionName sec) ++ " " ++ show (Elf.elfSectionSize sec)) seg
    let elfIdx = ElfSectionIndex (elfSectionIndex sec)
    let Just addr = resolveSegmentOff seg 0
    mlsIndexMap %= Map.insert elfIdx (addr, sec)

-- | Load allocated Elf sections into memory.
--
-- Normally, Elf uses segments for loading, but the segment
-- information tends to be more precise.
memoryForElfSections :: Elf w
                     -> MemLoader w ()
memoryForElfSections e = do
  traverseOf_ elfSections insertElfSection e

------------------------------------------------------------------------
-- High level loading

-- | Load allocated Elf sections into memory.
--
-- Normally, Elf uses segments for loading, but the segment
-- information tends to be more precise.
memoryForElf :: LoadOptions
             -> Elf w
             -> Either String (SectionIndexMap w, Memory w)
memoryForElf opt e =
  runMemLoader opt (emptyMemory (elfAddrWidth (elfClass e))) $ do
    case loadStyle opt of
      LoadBySection -> memoryForElfSections e
      LoadBySegment -> memoryForElfSegments e

-- | Pretty print parser errors to stderr.
ppErrors :: (Integral (ElfWordType w), Show (ElfWordType w))
         => FilePath
         -> [ElfParseError w]
         -> IO ()
ppErrors path errl = do
  when (not (null errl)) $ do
    hPutStrLn stderr $ "Non-fatal errors during parsing " ++ path
  forM_ errl $ \e -> do
    hPutStrLn stderr $ "  " ++ show e

-- | This reads the elf file from the given path.
--
-- As a side effect it may print warnings for errors encountered during parsing
-- to stderr.
readElf :: FilePath -> IO (SomeElf Elf)
readElf path = do
  bs <- BS.readFile path
  case Elf.parseElf bs of
    ElfHeaderError _ msg -> do
      fail $ "Could not parse Elf header: " ++ msg
    Elf32Res errl e -> do
      ppErrors path errl
      return (Elf32 e)
    Elf64Res errl e -> do
      ppErrors path errl
      return (Elf64 e)

loadExecutable :: LoadOptions ->  FilePath -> IO (Some Memory)
loadExecutable opt path = do
  se <- readElf path
  case se of
    Elf64 e -> either fail (return . Some . snd) $ memoryForElf opt e
    Elf32 e -> either fail (return . Some . snd) $ memoryForElf opt e

------------------------------------------------------------------------
-- Elf symbol utilities

-- | Error when resolving symbols.
data SymbolResolutionError
   = EmptySymbolName
     -- ^ Symbol names must be non-empty
   | CouldNotResolveAddr !BSC.ByteString
     -- ^ Symbol address could not be resolved.

instance Show SymbolResolutionError where
  show EmptySymbolName = "Found empty symbol name"
  show (CouldNotResolveAddr sym) = "Could not resolve address of " ++ BSC.unpack sym ++ "."

resolveEntry :: Memory w
             -> SectionIndexMap w
             -> ElfSymbolTableEntry (ElfWordType w)
             -> Maybe (Either SymbolResolutionError
                                (BS.ByteString, MemSegmentOff w))
resolveEntry mem secMap ste
  -- Check this is a defined function symbol
  | (Elf.steType ste `elem` [ Elf.STT_FUNC, Elf.STT_NOTYPE ]) == False = Nothing
    -- Check symbol is defined
  | Elf.steIndex ste == Elf.SHN_UNDEF = Nothing
  -- Check symbol name is non-empty
  | Elf.steName ste /= "" = Just (Left EmptySymbolName)
  -- Lookup absolute symbol
  | Elf.steIndex ste == Elf.SHN_ABS = reprConstraints (memAddrWidth mem) $ do
      let val = Elf.steValue ste
      case resolveAddr mem 0 (fromIntegral val) of
        Just addr -> Just $ Right (Elf.steName ste, addr)
        Nothing   -> Just $ Left $ CouldNotResolveAddr (Elf.steName ste)
  -- Lookup symbol stored in specific section
  | otherwise = reprConstraints (memAddrWidth mem) $ do
      let val = Elf.steValue ste
      case Map.lookup (Elf.steIndex ste) secMap of
        Just (base,sec)
          | elfSectionAddr sec <= val && val < elfSectionAddr sec + Elf.elfSectionSize sec
          , off <- toInteger (elfSectionAddr sec) - toInteger val
          , Just addr <- incSegmentOff base off -> do
              Just $ Right (Elf.steName ste, addr)
        _ -> Just $ Left $ CouldNotResolveAddr (Elf.steName ste)

-- | Resolve symbol table entries to the addresses in a memory.
--
-- It takes the memory constructed from the Elf file, the section
-- index map, and the symbol table entries.  It returns unresolvable
-- symbols and the map from segment offsets to bytestring.
resolveElfFuncSymbols
  :: forall w
  .  Memory w
  -> SectionIndexMap w
  -> [ElfSymbolTableEntry (ElfWordType w)]
  -> ( [SymbolResolutionError]
     , [(BS.ByteString, MemSegmentOff w)]
     )
resolveElfFuncSymbols mem secMap entries = reprConstraints (memAddrWidth mem) $
    partitionEithers (mapMaybe (resolveEntry mem secMap) entries)

ppElfUnresolvedSymbols :: forall w
                       .  MemWidth w
                       => Map (MemWord w) [BS.ByteString]
                       -> Doc
ppElfUnresolvedSymbols m =
    text "Could not resolve addresses of ELF symbols" <$$>
    indent 2 (vcat $ pp <$> Map.toList m)
  where pp :: (MemWord w, [BS.ByteString]) -> Doc
        pp (w, nms) = text (showHex w ":") <+> hsep (text . BSC.unpack <$> nms)
