{-# LANGUAGE FlexibleContexts #-}

module Data.Macaw.ARM.BinaryFormat.ELF
    ( getElfSections
    , getELFSymbols
    )
    where

import           Control.Lens ( (^.), (^..), to )
import           Data.Bits
import qualified Data.ByteString.Char8 as C8
import qualified Data.ElfEdit as E
import           Data.Vector (toList)
import           Text.PrettyPrint.ANSI.Leijen



getElfSections :: E.Elf w -> [String]
getElfSections e =
    e^..E.elfSections.to (C8.unpack . E.elfSectionName)


getELFSymbols :: (Show (E.ElfWordType w), Data.Bits.Bits (E.ElfWordType w), Integral (E.ElfWordType w)) => E.Elf w -> Doc
getELFSymbols elf =
    let symtab = elf^.to E.elfSymtab
        ps = fmap (E.ppSymbolTableEntries . toList . E.symtabEntries) symtab
    in vsep ps
