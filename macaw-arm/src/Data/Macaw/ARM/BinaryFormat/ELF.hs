{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Macaw.ARM.BinaryFormat.ELF
    ( getELFSymbols
    )
    where

import           Control.Lens ( (^.), to )
import           Data.Bits
import qualified Data.ElfEdit as E
import           Data.Vector (toList)
import           Text.PrettyPrint.ANSI.Leijen


getELFSymbols :: (Show (E.ElfWordType w), Data.Bits.Bits (E.ElfWordType w), Integral (E.ElfWordType w)) => E.Elf w -> Doc
getELFSymbols elf =
    let symtab = elf^.to E.elfSymtab
        ps = fmap (E.ppSymbolTableEntries . toList . E.elfSymbolTableEntries) symtab
    in vsep ps
