{-# LANGUAGE FlexibleContexts #-}

module Data.Macaw.ARM.BinaryFormat.ELF
    ( getElfSections
    , getELFSymbols
    )
    where

import           Data.Bits
import qualified Data.ByteString.Char8 as C8
import qualified Data.ElfEdit as E
import           Data.Vector (toList)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

getElfSections :: E.ElfHeaderInfo w -> [String]
getElfSections e =
  case E.headerNamedShdrs e of
    Left (_, msg) -> error $ show msg
    Right shdrs -> toList $ (C8.unpack . E.shdrName) <$> shdrs

getELFSymbols :: (Show (E.ElfWordType w), Data.Bits.Bits (E.ElfWordType w), Integral (E.ElfWordType w)) => E.ElfHeaderInfo w -> Doc
getELFSymbols elf =
  case E.decodeHeaderSymtab elf of
    Nothing -> empty
    Just (Left e) -> error (show e)
    Just (Right symtab) ->
      E.ppSymbolTableEntries (toList (E.symtabEntries symtab))
