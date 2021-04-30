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
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as E
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as NEL
import qualified Data.Macaw.BinaryLoader as BL
import qualified Data.Macaw.BinaryLoader.ELF as BLE
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as EL
import qualified Data.Macaw.Memory.LoadCommon as LC
import qualified Data.Map.Strict as Map
import           Data.Maybe ( mapMaybe )

import qualified Data.Macaw.X86 as MX

data X86ElfData w = X86ElfData { elf :: E.ElfHeaderInfo w
                               , memSymbols :: [EL.MemSymbol w]
                               , symbolIndex :: Map.Map (MM.MemAddr 64) BS.ByteString
                               }

instance BL.BinaryLoader MX.X86_64 (E.ElfHeaderInfo 64) where
  type ArchBinaryData MX.X86_64 (E.ElfHeaderInfo 64) = ()
  type BinaryFormatData MX.X86_64 (E.ElfHeaderInfo 64) = X86ElfData 64
  type Diagnostic MX.X86_64 (E.ElfHeaderInfo 64) = EL.MemLoadWarning
  loadBinary = loadX86Binary
  entryPoints = x86EntryPoints
  symbolFor = x86LookupSymbol

x86LookupSymbol :: (X.MonadThrow m)
                => BL.LoadedBinary MX.X86_64 (E.ElfHeaderInfo 64)
                -> MM.MemAddr 64
                -> m BS.ByteString
x86LookupSymbol loadedBinary addr =
  case Map.lookup addr (symbolIndex (BL.binaryFormatData loadedBinary)) of
    Just sym -> return sym
    Nothing -> X.throwM (MissingSymbolFor addr)

x86EntryPoints :: (X.MonadThrow m)
               => BL.LoadedBinary MX.X86_64 (E.ElfHeaderInfo 64)
               -> m (NEL.NonEmpty (MM.MemSegmentOff 64))
x86EntryPoints loadedBinary = do
  case BLE.resolveAbsoluteAddress mem addrWord of
    -- n.b. no guarantee of uniqueness, and in particular, entryPoint is probably in symbols somewhere
    Just entryPoint -> return (entryPoint NEL.:| mapMaybe (BLE.resolveAbsoluteAddress mem) symbolWords)
    Nothing -> X.throwM (InvalidEntryPoint addrWord)
  where
    mem = BL.memoryImage loadedBinary
    addrWord = MM.memWord (fromIntegral (E.headerEntry (E.header (elf (BL.binaryFormatData loadedBinary)))))
    elfData = elf (BL.binaryFormatData loadedBinary)
    symbolWords = [ MM.memWord (fromIntegral (E.steValue entry))
                  | Just (Right st) <- [E.decodeHeaderSymtab elfData]
                  , entry <- F.toList (E.symtabEntries st)
                  , E.steType entry == E.STT_FUNC
                  ]

loadX86Binary :: (X.MonadThrow m)
              => LC.LoadOptions
              -> E.ElfHeaderInfo 64
              -> m (BL.LoadedBinary MX.X86_64 (E.ElfHeaderInfo 64))
loadX86Binary lopts e = do
  case EL.memoryForElf lopts e of
    Left err -> X.throwM (X86ElfLoadError err)
    Right (mem, symbols, warnings, _) ->
      return BL.LoadedBinary { BL.memoryImage = mem
                             , BL.memoryEndianness = MM.LittleEndian
                             , BL.archBinaryData = ()
                             , BL.binaryFormatData =
                               X86ElfData { elf = e
                                          , memSymbols = symbols
                                          , symbolIndex = indexSymbols symbols
                                          }
                             , BL.loadDiagnostics = warnings
                             , BL.binaryRepr = BL.Elf64Repr
                             , BL.originalBinary = e
                             }

indexSymbols :: [EL.MemSymbol 64] -> Map.Map (MM.MemAddr 64) BS.ByteString
indexSymbols = F.foldl' doIndex Map.empty
  where
    doIndex m memSym =
      Map.insert (MM.segoffAddr (EL.memSymbolStart memSym)) (EL.memSymbolName memSym) m

data X86LoadException = X86ElfLoadError String
                      | InvalidEntryPoint (MM.MemWord 64)
                      | MissingSymbolFor (MM.MemAddr 64)

deriving instance Show X86LoadException

instance X.Exception X86LoadException
