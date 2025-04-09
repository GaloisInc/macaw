{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.Dump.Memory
  ( MemoryConfig(..)
  , memoryConfig
  , memory
  ) where

import Control.Monad as Monad
import Data.ByteString qualified as BS
import Data.ElfEdit qualified as EE
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.BinaryLoader qualified as Loader
import Data.Macaw.CFG.Core qualified as MC
import Data.Macaw.Dump.CLIUtils qualified as MDCU
import Data.Macaw.Memory.LoadCommon qualified as LC
import Data.Macaw.Memory qualified as MM
import Data.Word (Word8, Word64)
import Numeric (showHex)
import Options.Applicative qualified as Opt
import Prettyprinter qualified as PP

data MemoryConfig
  = MemoryConfig
    { memLoadOffset :: Maybe Word64
    , memPrintContents :: Bool
    , memBinPath :: FilePath
    }

loadOffsetOpt :: Opt.Parser Word64
loadOffsetOpt = Opt.option Opt.auto opts
  where
  opts =
    mconcat
    [ Opt.long "offset"
    , Opt.help "base offset at which to load the file"
    , Opt.showDefault
    ]

printContentsOpt :: Opt.Parser Bool
printContentsOpt = Opt.switch opts
  where
  opts =
    mconcat
    [ Opt.long "contents"
    , Opt.help "print the contents of memory"
    ]

memoryConfig :: Opt.Parser MemoryConfig
memoryConfig =
  MemoryConfig
  <$> Opt.optional loadOffsetOpt
  <*> printContentsOpt
  <*> MDCU.binOpt

loadOptions :: MemoryConfig -> LC.LoadOptions
loadOptions cfg = LC.LoadOptions { LC.loadOffset = memLoadOffset cfg }

ppChunk :: MM.MemChunk w -> PP.Doc ann
ppChunk =
  \case
    MM.ByteRegion bs -> PP.fillSep (map ppByte (BS.unpack bs))
    MM.RelocationRegion reloc -> PP.viaShow reloc
    MM.BSSRegion size ->
      PP.hcat
      [ PP.pretty "[bss,"
      , PP.pretty size
      , PP.pretty ']'
      ]
  where
    ppByte :: Word8 -> PP.Doc ann
    ppByte w | w < 16    = PP.pretty '0' <> PP.pretty (showHex w "")
             | otherwise = PP.pretty (showHex w "")

ppMemContent ::
  MM.MemWidth w =>
  MM.Memory w ->
  PP.Doc ann
ppMemContent mem =
  PP.vcat (map (uncurry printChunk) (MM.relativeSegmentContents (MM.memSegments mem)))
  where
  -- l = the max textual length of a 64-bit MemAddr (assuming < 10 regions)
  l = length "segmentN+0x0000000000000000"
  padr s =
    PP.hcat
    [ PP.pretty s
    , PP.pretty ": "
    , PP.hcat (replicate (l - length s) PP.space)
    ]
  printChunk addr chunk = padr (show addr) PP.<> PP.align (ppChunk chunk)

memory ::
  forall arch.
  ( MM.MemWidth (MC.ArchAddrWidth arch)
  , Loader.BinaryLoader arch (EE.ElfHeaderInfo (MC.ArchAddrWidth arch))
  ) =>
  MAI.ArchitectureInfo arch ->
  MemoryConfig ->
  IO ()
memory archInfo cfg = do
  ehi <- MDCU.loadElf archInfo (memBinPath cfg)
  let loadOpts = loadOptions cfg
  loaded <- Loader.loadBinary @arch loadOpts ehi
  let mem = Loader.memoryImage loaded
  print mem
  Monad.when (memPrintContents cfg) $ do
    putStrLn "\nContents:"
    print (ppMemContent mem)
