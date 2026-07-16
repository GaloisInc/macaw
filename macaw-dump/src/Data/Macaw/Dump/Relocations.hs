-- | Print relocations, similar to @readelf --relocs@

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.Dump.Relocations
  ( RelocationConfig(..)
  , relocationsConfig
  , relocations
  ) where

import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BSC
import Data.ElfEdit qualified as EE
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.BinaryLoader qualified as Loader
import Data.Macaw.CFG.Core qualified as MC
import Data.Macaw.Dump.CLIUtils qualified as MDCU
import Data.Macaw.Memory qualified as MM
import Data.Macaw.Memory.LoadCommon qualified as LC
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Vector qualified as V
import Data.Word (Word16, Word64)
import Numeric (showHex)
import Options.Applicative qualified as Opt
import Prettyprinter qualified as PP

data RelocationConfig
  = RelocationConfig
    { relocLoadOffset :: Maybe Word64
    , relocBinPath :: FilePath
    }

relocationsConfig :: Opt.Parser RelocationConfig
relocationsConfig =
  RelocationConfig
  <$> Opt.optional MDCU.loadOffsetOpt
  <*> MDCU.binOpt

loadOptions :: RelocationConfig -> LC.LoadOptions
loadOptions cfg = LC.LoadOptions { LC.loadOffset = relocLoadOffset cfg }

-- | Extract every relocation in the loaded memory image, paired with the
-- address it is stored at.
--
-- Relocations are not stored in a dedicated table on 'MM.Memory'; each is
-- embedded in a 'MM.RelocationRegion' chunk interleaved with the ordinary
-- byte and BSS chunks, so we walk the segment contents and keep the
-- relocation regions.
memRelocations :: MM.MemWidth w => MM.Memory w -> [(MM.MemAddr w, MM.Relocation w)]
memRelocations mem =
  [ (addr, reloc)
  | (addr, MM.RelocationRegion reloc) <-
      MM.relativeSegmentContents (MM.memSegments mem)
  ]

-- | Map each ELF section index to its name, drawn from the section header
-- string table.  Used to give 'MM.SectionIdentifier' relocations a
-- human-readable symbol.
sectionNames :: EE.ElfHeaderInfo w -> Map.Map Word16 BS.ByteString
sectionNames ehi =
  let (_, shstrtab) = EE.shstrtabRangeAndData ehi in
  Map.fromList
    [ (fromIntegral idx, nm)
    | (idx, shdr) <- zip [(0 :: Int) ..] (V.toList (EE.headerShdrs ehi))
    , Right nm <- [EE.lookupString (EE.shdrName shdr) shstrtab]
    ]

-- | Render the symbol a relocation is relative to, for the @Symbol@ column.
--
-- 'MM.SectionIdentifier's are resolved to a section name when one is known;
-- the remaining cases ('SymbolRelocation', 'SegmentBaseAddr', 'LoadBaseAddr')
-- already have informative 'Show' instances.
showSym :: Map.Map Word16 BS.ByteString -> MM.SymbolIdentifier -> String
showSym secNames =
  \case
    MM.SectionIdentifier idx
      | Just nm <- Map.lookup idx secNames ->
          BSC.unpack nm ++ " (section " ++ show idx ++ ")"
    sym -> show sym

-- | The @Flags@ column: a space-free summary of the boolean fields that the
-- abstract 'MM.Relocation' retains (the concrete relocation @Type@ is not
-- recoverable from it).  Renders @-@ when no flag is set.
relocFlags :: MM.Relocation w -> String
relocFlags r =
  case flags of
    [] -> "-"
    _  -> List.intercalate "|" flags
  where
  flags =
    concat
      [ [ "REL"     | MM.relocationIsRel r ]
      , [ "JMPSLOT" | MM.relocationJumpSlot r ]
      , [ "S"       | MM.relocationIsSigned r ]
      ]

-- | The @Endian@ column.
relocEndianness :: MM.Relocation w -> String
relocEndianness r =
  case MM.relocationEndianness r of
    MM.BigEndian    -> "BE"
    MM.LittleEndian -> "LE"

-- | One table row: @(offset, size, endian, flags, symbol + addend)@ as strings,
-- before column alignment.
relocRow ::
  MM.MemWidth w =>
  Map.Map Word16 BS.ByteString ->
  (MM.MemAddr w, MM.Relocation w) ->
  [String]
relocRow secNames (addr, r) =
  -- 'show addr' renders the full 'MM.MemAddr': a bare @0x...@ offset for an
  -- absolute (region 0) address, or @segmentN+0x...@ when the relocation lives
  -- in a relocatable region.
  [ show addr
  , show (MM.relocationSize r)
  , relocEndianness r
  , relocFlags r
  , showSym secNames (MM.relocationSym r)
      ++ " + 0x" ++ showHex (MM.memWordToUnsigned (MM.relocationOffset r)) ""
  ]

relocHeader :: [String]
relocHeader = ["Address", "Size", "Endian", "Flags", "Symbol + Addend"]

-- | Lay rows out as a left-aligned, space-padded table.  The final column is
-- not padded (nothing follows it).
ppTable :: [[String]] -> PP.Doc ann
ppTable rows =
  PP.vsep [ PP.pretty (List.intercalate "  " (padRow row)) | row <- rows ]
  where
  widths = map (maximum . (0 :) . map length) (List.transpose rows)
  -- Pad every cell to its column width except the last (nothing follows it,
  -- so padding it would only add trailing whitespace).
  padRow row = go (zip widths row)
    where
    go [] = []
    go [(_, cell)] = [cell]
    go ((w, cell) : rest) = pad w cell : go rest
  pad w s = s ++ replicate (w - length s) ' '

ppRelocations ::
  MM.MemWidth w =>
  EE.ElfHeaderInfo w ->
  MM.Memory w ->
  PP.Doc ann
ppRelocations ehi mem =
  case memRelocations mem of
    [] -> PP.pretty "No relocations found."
    relocs -> ppTable (relocHeader : map (relocRow secNames) relocs)
  where
  secNames = sectionNames ehi

relocations ::
  forall arch.
  ( MM.MemWidth (MC.ArchAddrWidth arch)
  , Loader.BinaryLoader arch (EE.ElfHeaderInfo (MC.ArchAddrWidth arch))
  ) =>
  MAI.ArchitectureInfo arch ->
  RelocationConfig ->
  IO ()
relocations archInfo cfg = do
  ehi <- MDCU.loadElf archInfo (relocBinPath cfg)
  loaded <- Loader.loadBinary @arch (loadOptions cfg) ehi
  let mem = Loader.memoryImage loaded
  print (ppRelocations ehi mem)
