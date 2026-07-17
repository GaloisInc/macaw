{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Golden tests for the @relocs@ subcommand of @macaw-x86-dump@.
--
-- These render the relocations of the binaries in the @macaw-x86@ and
-- @macaw-x86-symbolic@ test suites, and compare the output against checked-in
-- golden files.  Only binaries that actually contain relocations get a test;
-- the majority of the statically-linked executables have none.
module Relocs
  ( tests
  ) where

import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as LBS
import Control.Exception qualified as Exception
import Data.List qualified as List
import Data.Maybe (catMaybes)
import Data.Text qualified as T
import Data.Text.Encoding qualified as Text
import System.FilePath (takeFileName, (<.>))
import System.FilePath.Glob qualified as SFG

import Data.ElfEdit qualified as Elf
import Prettyprinter qualified as PP
import Prettyprinter.Render.Text qualified as PPT
import Test.Tasty qualified as TT
import Test.Tasty.Golden qualified as TTG

import Data.Macaw.Dump.Relocations qualified as MDR
import Data.Macaw.Memory qualified as MM
import Data.Macaw.Memory.ElfLoader qualified as MEL

-- | Collect every test binary from the @macaw-x86@ and @macaw-x86-symbolic@
-- suites and build a golden test for each one that contains relocations.
tests :: IO TT.TestTree
tests = do
  -- The @macaw-x86@ test suite runs with @x86@ as its working directory, so
  -- the @macaw-x86-symbolic@ binaries are reached via @..@.
  x86Bins <- concat <$> traverse SFG.glob
    [ "tests/x64/*.exe"
    , "tests/x64/*.o"
    ]
  symBins <- concat <$> traverse SFG.glob
    [ "../x86_symbolic/tests/pass/**/*.exe"
    , "../x86_symbolic/tests/fail/**/*.exe"
    ]
  let testCases = map (\path -> (path, path)) (x86Bins ++ symBins)
               ++ [ ( "../deps/elf-edit/tests/relocs/x86_64/relocs.o"
                    , "tests/x64/relocs.o"
                    )
                  ]
  relocTests <- traverse (uncurry mkRelocTest) (List.sort testCases)
  pure (TT.testGroup "relocs golden tests" (catMaybes relocTests))

-- | Build a golden test for a single binary, or 'Nothing' if it cannot be
-- loaded as a 64-bit x86 ELF file or has no relocations.
mkRelocTest :: FilePath -> FilePath -> IO (Maybe TT.TestTree)
mkRelocTest path goldenPath = do
  bytes <- BS.readFile path
  case Elf.decodeElfHeaderInfo bytes of
    Left _ -> pure Nothing
    Right (Elf.SomeElf ehi) ->
      case Elf.headerClass (Elf.header ehi) of
        Elf.ELFCLASS32 -> pure Nothing
        Elf.ELFCLASS64 -> loadRelocs path goldenPath ehi

loadRelocs :: MM.MemWidth w
           => FilePath
           -> FilePath
           -> Elf.ElfHeaderInfo w
           -> IO (Maybe TT.TestTree)
loadRelocs path goldenPath ehi =
  fmap (goldenTest path goldenPath) <$> renderRelocs ehi

renderRelocs :: MM.MemWidth w => Elf.ElfHeaderInfo w -> IO (Maybe LBS.ByteString)
renderRelocs ehi = do
  result <-
    (Exception.try (Exception.evaluate (forceOutput output))
      :: IO (Either Exception.ErrorCall (Maybe LBS.ByteString)))
  pure $ case result of
    Left err -> Just (errorOutput (exceptionMessage err))
    Right output' -> output'
  where
  output =
    case MEL.resolveElfContents (loadOptions ehi) ehi of
      Left err -> Just (errorOutput err)
      Right (warnings, mem, _entry, _symbols)
        | null (MDR.memRelocations mem) -> Nothing
        | otherwise -> Just (render (withWarnings warnings (MDR.ppRelocations ehi mem)))

forceOutput :: Maybe LBS.ByteString -> Maybe LBS.ByteString
forceOutput output =
  case output of
    Nothing -> Nothing
    Just bytes -> LBS.length bytes `seq` output

errorOutput :: String -> LBS.ByteString
errorOutput err =
  LBS.fromStrict (Text.encodeUtf8 ("ERROR: " <> T.pack err <> "\n"))

exceptionMessage :: Exception.ErrorCall -> String
exceptionMessage = takeWhile (/= '\n') . Exception.displayException

withWarnings :: [String] -> PP.Doc ann -> PP.Doc ann
withWarnings warnings doc =
  case warnings of
    [] -> doc
    _ -> doc <> PP.hardline <> PP.pretty ("Warnings:" :: String) <> PP.hardline
           <> PP.vsep (PP.pretty <$> warnings)

loadOptions :: Elf.ElfHeaderInfo w -> MEL.LoadOptions
loadOptions ehi
  | Elf.headerType (Elf.header ehi) == Elf.ET_REL = MEL.defaultLoadOptions
  | otherwise = MEL.defaultLoadOptions { MEL.loadOffset = Just 0 }

goldenTest :: FilePath -> FilePath -> LBS.ByteString -> TT.TestTree
goldenTest path goldenPath output =
  TTG.goldenVsStringDiff
    (takeFileName path)
    (\ref new -> ["diff", "-u", ref, new])
    (goldenPath <.> "relocs")
    (pure output)

render :: PP.Doc ann -> LBS.ByteString
render d =
  LBS.fromStrict
    (Text.encodeUtf8
      (PPT.renderStrict (PP.layoutPretty PP.defaultLayoutOptions d) <> "\n"))
