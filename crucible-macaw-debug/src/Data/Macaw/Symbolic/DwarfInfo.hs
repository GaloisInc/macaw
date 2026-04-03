{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Symbolic.DwarfInfo
  ( DwarfInfoCache
  , SourceLocation(..)
  , newDwarfInfoCache
  , newDwarfInfoCacheFromElf
  , lookupSourceLocation
  ) where

import Control.Monad (guard)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Dwarf qualified as Dwarf
import Data.ElfEdit qualified as Data.ElfEdit
import Data.IntervalMap.Interval qualified as IMI
import Data.IntervalMap.Strict qualified as IM
import Data.IORef (IORef)
import Data.IORef qualified as IORef
import Data.Macaw.Dwarf qualified as D
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, listToMaybe)
import Data.Vector qualified as V
import Data.Word (Word64)
import GHC.TypeNats (type (<=))

-- | Per-compile-unit cached IntervalMaps
data CompileUnitInfo = CompileUnitInfo
  { cumLineNumberMap :: !(IM.IntervalMap Word64 (Dwarf.DW_LNE, D.FileVec))
  , cumSubprogramMap :: !(IM.IntervalMap Word64 D.Subprogram)
  }

-- | Lazy cache for DWARF information
data DwarfInfoCache = DwarfInfoCache
  { dicCompileUnits :: ![D.CompileUnit]
  , dicCachedMaps :: !(IORef (Map Int CompileUnitInfo))
  }

-- | Source location information extracted from DWARF
data SourceLocation = SourceLocation
  { slFile :: !ByteString
  , slLine :: !Word64
  , slColumn :: !Word64
  , slAddress :: !Word64
  , slFunction :: !(Maybe ByteString)
  }
  deriving (Show)

-- | Initialize a new DWARF info cache with empty map
newDwarfInfoCache :: [D.CompileUnit] -> IO DwarfInfoCache
newDwarfInfoCache cus = do
  cacheRef <- IORef.newIORef Map.empty
  pure $ DwarfInfoCache
    { dicCompileUnits = cus
    , dicCachedMaps = cacheRef
    }

-- | Create a DWARF info cache from an ELF file (or Nothing if no debug info)
newDwarfInfoCacheFromElf ::
  forall w. (1 <= w) =>
  Data.ElfEdit.Elf w ->
  IO (Maybe DwarfInfoCache)
newDwarfInfoCacheFromElf elf =
  let (_, cus) = D.dwarfInfoFromElf elf
      hasDwarfInfo = not (null cus) && not (all (null . D.cuLNE) cus)
  in if hasDwarfInfo
     then Just <$> newDwarfInfoCache cus
     else pure Nothing

-- | Check if an address is within a DWARF range
addressInRange :: Word64 -> Dwarf.Range -> Bool
addressInRange addr (Dwarf.Range begin end) =
  addr >= begin && addr < end

-- | Find which compile unit contains the given address
findCompileUnitIndex :: Word64 -> [D.CompileUnit] -> Maybe (Int, D.CompileUnit)
findCompileUnitIndex addr cus =
  listToMaybe [(idx, cu) | (idx, cu) <- zip [0..] cus
                         , any (addressInRange addr) (D.cuRanges cu)]

-- | Build IntervalMaps for a single compile unit
buildCompileUnitInfo :: D.CompileUnit -> CompileUnitInfo
buildCompileUnitInfo cu =
  CompileUnitInfo
    { cumLineNumberMap = buildLineNumberMapForCU cu
    , cumSubprogramMap = buildSubprogramMapForCU cu
    }

-- | Build line number IntervalMap for a single compile unit
buildLineNumberMapForCU :: D.CompileUnit -> IM.IntervalMap Word64 (Dwarf.DW_LNE, D.FileVec)
buildLineNumberMapForCU cu =
  let entries = D.cuLNE cu
      fileVec = D.cuFileVec cu
      nonEndSeq = filter (not . Dwarf.lnmEndSequence) entries
      intervals = case nonEndSeq of
        [] -> []
        (_:rest) -> zipWith (buildInterval fileVec) nonEndSeq rest
  in IM.fromList (catMaybes intervals)
  where
    buildInterval fileVec entry nextEntry = do
      guard (not . Dwarf.lnmEndSequence $ entry)
      let interval = IMI.ClosedInterval (Dwarf.lnmAddress entry) (Dwarf.lnmAddress nextEntry - 1)
      pure (interval, (entry, fileVec))

-- | Build subprogram IntervalMap for a single compile unit
buildSubprogramMapForCU :: D.CompileUnit -> IM.IntervalMap Word64 D.Subprogram
buildSubprogramMapForCU cu =
  let subprograms = D.cuSubprograms cu
      intervals = catMaybes $ map subprogramToInterval subprograms
  in IM.fromList intervals
  where
    subprogramToInterval sub = do
      def <- D.subDef sub
      lowPC <- D.subLowPC def
      highPC <- D.subHighPC def
      let interval = IMI.ClosedInterval lowPC (highPC - 1)
      pure (interval, sub)

-- | Get or compute maps for a compile unit (with thread-safe caching)
getOrComputeMaps :: DwarfInfoCache -> Int -> D.CompileUnit -> IO CompileUnitInfo
getOrComputeMaps cache cuIdx cu = do
  cacheMap <- IORef.readIORef (dicCachedMaps cache)
  case Map.lookup cuIdx cacheMap of
    Just maps -> pure maps  -- Already cached
    Nothing -> do
      -- Build maps for this CU
      let maps = buildCompileUnitInfo cu
      -- Atomically insert into cache (idempotent if concurrent)
      IORef.atomicModifyIORef' (dicCachedMaps cache) $ \m ->
        (Map.insert cuIdx maps m, maps)

-- | Extract source location from DWARF structures
extractSourceLocation ::
  Maybe (Dwarf.DW_LNE, D.FileVec) ->
  Maybe D.Subprogram ->
  Maybe SourceLocation
extractSourceLocation lineInfo subprogramInfo = do
  (entry, fileVec) <- lineInfo
  let fileIdx = Dwarf.lnmFile entry
  guard (fileIdx > 0 && fileIdx <= fromIntegral (V.length fileVec))
  let filePath = D.filePathVal (fileVec V.! fromIntegral (fileIdx - 1))

  let functionName = case subprogramInfo of
        Just sub ->
          let fnName = D.nameVal (D.subName sub)
          in if BS.null fnName then Nothing else Just fnName
        Nothing -> Nothing

  pure $ SourceLocation
    { slFile = filePath
    , slLine = Dwarf.lnmLine entry
    , slColumn = Dwarf.lnmColumn entry
    , slAddress = Dwarf.lnmAddress entry
    , slFunction = functionName
    }

-- | Look up source location for a given address (with lazy per-CU computation)
lookupSourceLocation :: DwarfInfoCache -> Word64 -> IO (Maybe SourceLocation)
lookupSourceLocation cache addr = do
  -- Find which compile unit contains this address
  case findCompileUnitIndex addr (dicCompileUnits cache) of
    Nothing -> pure Nothing  -- Address not in any CU
    Just (cuIdx, cu) -> do
      -- Get or compute maps for this CU
      maps <- getOrComputeMaps cache cuIdx cu

      -- Look up in both maps
      let lineInfo = fmap snd $ listToMaybe $ IM.toList $ IM.containing (cumLineNumberMap maps) addr
          subprogramInfo = fmap snd $ listToMaybe $ IM.toList $ IM.containing (cumSubprogramMap maps) addr

      pure $ extractSourceLocation lineInfo subprogramInfo
