{-|
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
  , memoryForElf
  , resolveElfFuncSymbols
  , initElfDiscoveryInfo
  , module Data.Macaw.Memory.LoadCommon
  ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Data.Bits
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
import           Data.Int (Int64)
import           Data.IntervalMap.Strict (Interval(..), IntervalMap)
import qualified Data.IntervalMap.Strict as IMap
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Vector as V

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
-- Loading by segment

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

-- | Flag to control whether we include BSS
type IncludeBSS = Bool

-- | Pad zeros if we includ eBSS
padBSSData :: IncludeBSS -> L.ByteString -> Int64 -> L.ByteString
padBSSData incBSS dta sz
  | L.length dta > sz = L.take sz dta
  | incBSS = dta `mappend` L.replicate (sz - L.length dta) 0
  | otherwise = dta

-- | Return a memory segment for elf segment if it loadable.
memSegmentForElfSegment :: (MemWidth w, Integral (ElfWordType w))
                        => RegionIndex -- ^ Index for segment
                        -> IncludeBSS -- ^ Flag to control wheter we include BSS
                        -> L.ByteString
                           -- ^ Complete contents of Elf file.
                        -> RelocMap (MemWord w)
                           -- ^ Relocation map
                        -> Elf.Phdr w
                           -- ^ Program header entry
                        -> MemSegment w
memSegmentForElfSegment regIdx incBSS contents relocMap phdr = mseg
  where seg = Elf.phdrSegment phdr
        dta = sliceL (Elf.phdrFileRange phdr) contents
        sz = fromIntegral $ Elf.phdrMemSize phdr
        fixedData = padBSSData incBSS dta sz
        addr = fromIntegral $ elfSegmentVirtAddr seg
        flags = flagsForSegmentFlags (elfSegmentFlags seg)
        mseg = memSegment regIdx addr flags (byteSegments relocMap addr fixedData)

-- | Create memory segment from elf section.
--
-- This returns `Nothing` if the memory segment is empty.
-- TODO: Evaluate whether we should do the same for memSegmentForElfSegment, and
-- whether we should add relocations.
memSegmentForElfSection :: (Integral v, Bits v, MemWidth w)
                        => RegionIndex -- ^ Index for segment
                        -> Bool -- ^ Flag to control wheter we include BSS
                        -> ElfSection v
                        -> Maybe (MemSegment w)
memSegmentForElfSection regIdx incBSS s
  | L.length fixedData == 0 = Nothing
  | otherwise = Just (memSegment regIdx base flags [ByteRegion $ L.toStrict fixedData])
  where base = fromIntegral (elfSectionAddr s)
        flags = flagsForSectionFlags (elfSectionFlags s)
        bytes = elfSectionData s
        fixedData = padBSSData incBSS (L.fromStrict bytes) (fromIntegral (Elf.elfSectionSize s))

------------------------------------------------------------------------
-- MemLoader

data MemLoaderState w = MLS { mlsRegionIndex :: !RegionIndex
                              -- ^ Region index for new segments
                            , mlsIncludeBSS  :: !Bool
                              -- ^ Flag whether to include BSS
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

runMemLoader :: RegionIndex -> Bool -> Memory  w -> MemLoader w () -> Either String (SectionIndexMap w, Memory w)
runMemLoader regIdx incBSS mem m = fmap memLoaderPair $ runExcept $ execStateT m s
   where s = MLS { mlsRegionIndex = regIdx
                 , mlsIncludeBSS = incBSS
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

-- | Given a relocation entry, this returns either @Left msg@ if the relocation
-- cannot be resolved, @Right Nothing@ if
relaTarget :: V.Vector SymbolRef
                 -- ^ Get c
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

relocEntry :: V.Vector SymbolRef
           -> Elf.RelaEntry Elf.X86_64_RelocationType
           -> Either String (Maybe (MemWord 64, SymbolRef))
relocEntry symtab rel = fmap (fmap f) $ relaTarget symtab rel
  where f :: SymbolRef -> (MemWord 64, SymbolRef)
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
relocMapOfDynamic :: Elf.ElfHeader w
                  -> Elf.VirtAddrMap w
                  -> L.ByteString -- ^ Contents of .dynamic section
                  -> MemLoader w (RelocMap (MemWord w))
relocMapOfDynamic hdr virtMap dynContents =
  case (Elf.headerClass hdr, Elf.headerMachine hdr) of
    (Elf.ELFCLASS64, Elf.EM_X86_64) -> do
      dynSection <- either (throwError . show) pure $
        Elf.dynamicEntries (Elf.headerData hdr) Elf.ELFCLASS64 virtMap dynContents
      relocs <- either (throwError . show) pure $
        Elf.dynRelocations (dynSection :: Elf.DynamicSection Elf.X86_64_RelocationType)
      syms <- either (throwError . show) pure $
        Elf.dynSymTable dynSection
      either throwError pure $
        mkRelocMap (mkSymbolRef <$> syms) relocs
    (_,mach) -> throwError $ "Dynamic libraries are not supported on " ++ show mach ++ "."

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
  regIdx <- gets mlsRegionIndex
  incBSS <- gets mlsIncludeBSS
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
  let seg = memSegmentForElfSegment regIdx incBSS contents relocMap phdr
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
  let ph  = Elf.allPhdrs l
  let contents = elfLayoutBytes l
  virtMap <- maybe (throwError "Overlapping loaded segments") pure $
    Elf.virtAddrMap contents ph
  relocMap <-
    case filter (Elf.hasSegmentType Elf.PT_DYNAMIC . Elf.phdrSegment) ph of
      [] -> pure Map.empty
      [dynPhdr] -> do
        let dynContents = sliceL (Elf.phdrFileRange dynPhdr) contents
        relocMapOfDynamic (Elf.elfHeader e) virtMap dynContents
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
  regIdx <- gets mlsRegionIndex
  incBSS <- gets mlsIncludeBSS
  w <- uses mlsMemory memAddrWidth
  reprConstraints w $ do
  -- Check if we should load section
  let doLoad = elfSectionFlags sec `Elf.hasPermissions` Elf.shf_alloc
            && elfSectionName sec /= ".eh_frame"
  case memSegmentForElfSection regIdx incBSS sec of
    Just seg | doLoad -> do
      loadMemSegment ("Section " ++ BSC.unpack (elfSectionName sec) ++ " " ++ show (Elf.elfSectionSize sec)) seg
      let elfIdx = ElfSectionIndex (elfSectionIndex sec)
      let Just addr = resolveSegmentOff seg 0
      mlsIndexMap %= Map.insert elfIdx (addr, sec)
    _ -> pure ()

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

adjustedLoadStyle :: Elf w -> LoadOptions -> LoadStyle
adjustedLoadStyle e loadOpt =
  case loadStyleOverride loadOpt of
    Just sty -> sty
    Nothing ->
      case Elf.elfType e of
        Elf.ET_REL -> LoadBySection
        _ -> LoadBySegment

-- | Load allocated Elf sections into memory.
--
-- Normally, Elf uses segments for loading, but the segment
-- information tends to be more precise.
memoryForElf :: LoadOptions
             -> Elf w
             -> Either String (SectionIndexMap w, Memory w)
memoryForElf opt e = do
  let regIdx = adjustedLoadRegionIndex e opt
  runMemLoader regIdx (includeBSS opt) (emptyMemory (elfAddrWidth (elfClass e))) $ do
    case adjustedLoadStyle e opt of
      LoadBySection -> memoryForElfSections e
      LoadBySegment -> memoryForElfSegments e

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

-- | Resolve symbol table entries to the addresses in a memory.
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

------------------------------------------------------------------------
-- initElfDiscoveryInfo

-- | Return the segment offset of the elf file entry point or fail if undefined.
getElfEntry ::  Memory w -> Elf w -> Either String (MemSegmentOff w)
getElfEntry mem e =  addrWidthClass (memAddrWidth mem) $ do
 Elf.elfClassInstances (Elf.elfClass e) $ do
  case resolveAbsoluteAddr mem (fromIntegral (Elf.elfEntry e)) of
    Nothing -> Left "Could not resolve entry"
    Just v  -> Right v

-- | This interprets the Elf file to construct the initial memory,
-- entry points, and functions symbols.
--
-- If it encounters a fatal error it returns the error message in the left value,
-- and otherwise it returns the information interred as a 4-tuple.
initElfDiscoveryInfo :: LoadOptions
                        -- ^ Options for loading contents
                     -> Elf w -- ^ Elf file to create memory
                     -> Either String
                           ( [String] -- Warnings
                           , Memory w -- Initial memory
                           , Maybe (MemSegmentOff w) -- Entry point(s)
                           , [MemSymbol w] -- Function symbols
                           )
initElfDiscoveryInfo loadOpts e = do
  case Elf.elfType e of
    Elf.ET_REL -> do
      case loadStyleOverride loadOpts of
        Just LoadBySegment -> do
          Left $ "Cannot load object files by segment."
        _ -> pure ()
      (secMap, mem) <- memoryForElf loadOpts e
      let (symErrs, funcSymbols) = resolveElfFuncSymbols mem secMap e
      pure (show <$> symErrs, mem, Nothing, funcSymbols)
    Elf.ET_EXEC -> do
      (secMap, mem) <- memoryForElf loadOpts e
      entry <- getElfEntry mem e
      let (symErrs, funcSymbols) = resolveElfFuncSymbols mem secMap e
      Right (show <$> symErrs, mem, Just entry, funcSymbols)
    Elf.ET_DYN -> do
      (secMap, mem) <- memoryForElf loadOpts e
      entry <- getElfEntry mem e
      let (symErrs, funcSymbols) = resolveElfFuncSymbols mem secMap e
      pure (show <$> symErrs, mem, Just entry, funcSymbols)
    Elf.ET_CORE -> do
      Left $ "Reopt does not support loading core files."
    tp -> do
      Left $ "Reopt does not support loading elf files with type " ++ show tp ++ "."
