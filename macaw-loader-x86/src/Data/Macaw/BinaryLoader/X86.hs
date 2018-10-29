{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Macaw.BinaryLoader.X86 (
  X86LoadException(..)
  ) where

import qualified Control.Monad.Catch as X
import qualified Data.ElfEdit as E
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as NEL
import qualified Data.Macaw.BinaryLoader as BL
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as EL
import qualified Data.Macaw.Memory.LoadCommon as LC
import           Data.Maybe ( mapMaybe )

import qualified Data.Macaw.X86 as MX

data X86ElfData w = X86ElfData { elf :: E.Elf w
                               , memSymbols :: [EL.MemSymbol w]
                               }

instance BL.BinaryLoader MX.X86_64 (E.Elf 64) where
  type ArchBinaryData MX.X86_64 (E.Elf 64) = ()
  type BinaryFormatData MX.X86_64 (E.Elf 64) = X86ElfData 64
  type Diagnostic MX.X86_64 (E.Elf 64) = EL.MemLoadWarning
  type BinaryAddrWidth (E.Elf 64) = 64
  loadBinary = loadX86Binary
  entryPoints = x86EntryPoints

x86EntryPoints :: (X.MonadThrow m)
               => BL.LoadedBinary MX.X86_64 (E.Elf 64)
               -> m (NEL.NonEmpty (MM.MemSegmentOff 64))
x86EntryPoints loadedBinary = do
  case MM.asSegmentOff mem addr of
    Just entryPoint -> return (entryPoint NEL.:| mapMaybe (MM.asSegmentOff mem) symbols)
    Nothing -> X.throwM (InvalidEntryPoint addr)
  where
    mem = BL.memoryImage loadedBinary
    addr = MM.absoluteAddr (MM.memWord (fromIntegral (E.elfEntry (elf (BL.binaryFormatData loadedBinary)))))
    elfData = elf (BL.binaryFormatData loadedBinary)
    symbols = [ MM.absoluteAddr (MM.memWord (fromIntegral (E.steValue entry)))
              | st <- E.elfSymtab elfData
              , entry <- F.toList (E.elfSymbolTableEntries st)
              , E.steType entry == E.STT_FUNC
              ]

loadX86Binary :: (X.MonadThrow m)
              => LC.LoadOptions
              -> E.Elf 64
              -> m (BL.LoadedBinary MX.X86_64 (E.Elf 64))
loadX86Binary lopts e = do
  case EL.memoryForElf lopts e of
    Left err -> X.throwM (X86ElfLoadError err)
    Right (mem, symbols, warnings, _) ->
      return BL.LoadedBinary { BL.memoryImage = mem
                             , BL.archBinaryData = ()
                             , BL.binaryFormatData =
                               X86ElfData { elf = e
                                          , memSymbols = symbols
                                          }
                             , BL.loadDiagnostics = warnings
                             , BL.binaryRepr = BL.Elf64Repr
                             }

data X86LoadException = X86ElfLoadError String
                      | forall w . (MM.MemWidth w) => InvalidEntryPoint (MM.MemAddr w)

deriving instance Show X86LoadException

instance X.Exception X86LoadException
