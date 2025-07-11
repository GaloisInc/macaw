{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.BinaryLoader.AArch32 (
  AArch32LoadException(..)
  ) where

import qualified Control.Monad.Catch as X
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as EE
import qualified Data.Foldable as F
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.BinaryLoader.ELF as BLE
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as EL
import qualified Data.Macaw.Memory.LoadCommon as LC
import qualified Data.Map.Strict as Map
import           Data.Maybe ( catMaybes, fromMaybe )
import           Data.Word ( Word32 )

import qualified Data.Macaw.ARM as MA

data AArch32ElfData =
  AArch32ElfData { elf :: EE.ElfHeaderInfo 32
                 , memSymbols :: [EL.MemSymbol 32]
                 , symbolIndex :: Map.Map (MM.MemAddr 32) BS.ByteString
                 }

instance MBL.BinaryLoader MA.ARM (EE.ElfHeaderInfo 32) where
  type ArchBinaryData MA.ARM (EE.ElfHeaderInfo 32) = ()
  type BinaryFormatData MA.ARM (EE.ElfHeaderInfo 32) = AArch32ElfData
  type Diagnostic MA.ARM (EE.ElfHeaderInfo 32) = EL.MemLoadWarning
  loadBinary = loadAArch32Binary
  entryPoints = aarch32EntryPoints
  symbolFor = aarch32LookupSymbol

aarch32LookupSymbol :: (X.MonadThrow m)
                    => MBL.LoadedBinary MA.ARM (EE.ElfHeaderInfo 32)
                    -> MM.MemAddr 32
                    -> m BS.ByteString
aarch32LookupSymbol loadedBinary addr =
  case Map.lookup addr (symbolIndex (MBL.binaryFormatData loadedBinary)) of
    Just sym -> return sym
    Nothing -> X.throwM (MissingSymbolFor addr)

aarch32EntryPoints :: (X.MonadThrow m)
                   => MBL.LoadedBinary MA.ARM (EE.ElfHeaderInfo 32)
                   -> m [MM.MemSegmentOff 32]
aarch32EntryPoints loadedBinary =
  -- n.b. no guarantee of uniqueness, and in particular, `headerEntryPoint` is
  -- probably in `symbolEntryPoints` somewhere
  return $ catMaybes $ headerEntryPoint : symbolEntryPoints
  where
    headerEntryPoint = BLE.resolveAbsoluteAddress mem addr
    symbolEntryPoints = map (BLE.resolveAbsoluteAddress mem) symbols

    offset = fromMaybe 0 (LC.loadOffset (MBL.loadOptions loadedBinary))
    mem = MBL.memoryImage loadedBinary
    addr = MM.memWord (offset + fromIntegral (EE.headerEntry (EE.header (elf (MBL.binaryFormatData loadedBinary)))))
    elfData = elf (MBL.binaryFormatData loadedBinary)
    staticSyms = symtabEntriesList $ EE.decodeHeaderSymtabLenient elfData
    dynSyms = symtabEntriesList $ EE.decodeHeaderDynsymLenient elfData
    symbols = [ MM.memWord (offset + fromIntegral (EE.steValue entry))
              | entry <- staticSyms ++ dynSyms
              , EE.steType entry == EE.STT_FUNC
              ]

    symtabEntriesList :: Either EE.SymtabError (Maybe (EE.Symtab 32))
                      -> [EE.SymtabEntry BS.ByteString Word32]
    symtabEntriesList symtab =
      case symtab of
        Left _ -> []
        Right Nothing -> []
        Right (Just st) -> F.toList (EE.symtabEntries st)

loadAArch32Binary :: (X.MonadThrow m)
                  => LC.LoadOptions
                  -> EE.ElfHeaderInfo 32
                  -> m (MBL.LoadedBinary MA.ARM (EE.ElfHeaderInfo 32))
loadAArch32Binary lopts e =
  case EL.memoryForElf lopts e of
    Left err -> X.throwM (AArch32ElfLoadError err)
    Right (mem, symbols, warnings, _) ->
      return MBL.LoadedBinary { MBL.memoryImage = mem
                              , MBL.memoryEndianness = MM.LittleEndian
                              , MBL.archBinaryData = ()
                              , MBL.binaryFormatData =
                                AArch32ElfData { elf = e
                                               , memSymbols = symbols
                                               , symbolIndex = indexSymbols symbols
                                               }
                              , MBL.loadDiagnostics = warnings
                              , MBL.binaryRepr = MBL.Elf32Repr
                              , MBL.originalBinary = e
                              , MBL.loadOptions = lopts
                              }

indexSymbols :: [EL.MemSymbol 32] -> Map.Map (MM.MemAddr 32) BS.ByteString
indexSymbols = F.foldl' doIndex Map.empty
  where
    doIndex m memSym =
      Map.insert (MM.segoffAddr (EL.memSymbolStart memSym)) (EL.memSymbolName memSym) m

data AArch32LoadException = AArch32ElfLoadError String
                          | MissingSymbolFor (MM.MemAddr 32)

deriving instance Show AArch32LoadException

instance X.Exception AArch32LoadException
