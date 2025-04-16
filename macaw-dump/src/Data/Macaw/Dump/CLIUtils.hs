{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Data.Macaw.Dump.CLIUtils
  ( binOpt
  , loadOffsetOpt
  , die
  , loadElf
  ) where

import Data.ByteString qualified as BS
import Data.ElfEdit qualified as EE
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.CFG qualified as MC
import Data.Macaw.Memory qualified as MM
import Data.Word (Word64)
import Options.Applicative qualified as Opt
import System.Exit qualified as Exit
import System.IO qualified as IO

binOpt :: Opt.Parser FilePath
binOpt = Opt.strArgument (Opt.help "filename of binary" <> Opt.metavar "FILENAME" )

loadOffsetOpt :: Opt.Parser Word64
loadOffsetOpt = Opt.option Opt.auto opts
  where
  opts =
    mconcat
    [ Opt.long "offset"
    , Opt.help "base offset at which to load the file"
    , Opt.showDefault
    ]

die :: String -> IO a
die msg = do
  IO.hPutStrLn IO.stderr msg
  Exit.exitFailure

loadElf ::
  MAI.ArchitectureInfo arch ->
  FilePath ->
  IO (EE.ElfHeaderInfo (MC.ArchAddrWidth arch))
loadElf archInfo elfPath = do
  bytes <- BS.readFile elfPath
  case EE.decodeElfHeaderInfo bytes of
    Left (_, msg) -> die ("Error parsing ELF header from file '" ++ elfPath ++ "': " ++ msg)
    Right (EE.SomeElf ehi) -> do
      case MAI.archAddrWidth archInfo of
        MM.Addr32 ->
          case EE.headerClass (EE.header ehi) of
            EE.ELFCLASS32 -> pure ehi
            EE.ELFCLASS64 -> die "Expected 32-bit ELF file, found 64-bit"
        MM.Addr64 ->
          case EE.headerClass (EE.header ehi) of
            EE.ELFCLASS32 -> die "Expected 64-bit ELF file, found 32-bit"
            EE.ELFCLASS64 -> pure ehi
