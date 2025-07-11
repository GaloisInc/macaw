{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Macaw.BinaryLoader.RISCV (
  RISCVLoadException(..)
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
import qualified GRIFT.Types as G

import qualified Data.Macaw.RISCV as MR

data RISCVElfData w =
  RISCVElfData { elf :: EE.ElfHeaderInfo w
               , memSymbols :: [EL.MemSymbol w]
               , symbolIndex :: Map.Map (MM.MemAddr w) BS.ByteString
               }

instance (w ~ G.RVWidth rv, MR.RISCVConstraints rv)
    => MBL.BinaryLoader (MR.RISCV rv) (EE.ElfHeaderInfo w) where
  type ArchBinaryData (MR.RISCV rv) (EE.ElfHeaderInfo w) = ()
  type BinaryFormatData (MR.RISCV rv) (EE.ElfHeaderInfo w) = RISCVElfData w
  type Diagnostic (MR.RISCV rv) (EE.ElfHeaderInfo w) = EL.MemLoadWarning
  loadBinary = loadRiscvBinary
  entryPoints = riscvEntryPoints
  symbolFor = riscvLookupSymbol

riscvLookupSymbol :: (X.MonadThrow m)
                  => MBL.LoadedBinary (MR.RISCV rv) (EE.ElfHeaderInfo (G.RVWidth rv))
                  -> MM.MemAddr (G.RVWidth rv)
                  -> m BS.ByteString
riscvLookupSymbol loadedBinary addr =
  case Map.lookup addr (symbolIndex (MBL.binaryFormatData loadedBinary)) of
    Just sym -> return sym
    Nothing -> X.throwM (MissingSymbolFor addr)

riscvEntryPoints :: forall m rv
                  . (X.MonadThrow m, MR.RISCVConstraints rv)
                 => MBL.LoadedBinary (MR.RISCV rv) (EE.ElfHeaderInfo (G.RVWidth rv))
                 -> m [MM.MemSegmentOff (G.RVWidth rv)]
riscvEntryPoints loadedBinary =
  EE.elfClassInstances elfClass $
  let addr = MM.memWord (offset + fromIntegral (EE.headerEntry (EE.header (elf (MBL.binaryFormatData loadedBinary))))) in
  let symbols = [ MM.memWord (offset + fromIntegral (EE.steValue entry))
                | entry <- staticSyms ++ dynSyms
                , EE.steType entry == EE.STT_FUNC
                ] in
  let headerEntryPoint = BLE.resolveAbsoluteAddress mem addr in
  let symbolEntryPoints = map (BLE.resolveAbsoluteAddress mem) symbols in
  -- n.b. no guarantee of uniqueness, and in particular, `headerEntryPoint` is
  -- probably in `symbolEntryPoints` somewhere
  return $ catMaybes $ headerEntryPoint : symbolEntryPoints
  where
    offset = fromMaybe 0 (LC.loadOffset (MBL.loadOptions loadedBinary))
    mem = MBL.memoryImage loadedBinary
    elfData = elf (MBL.binaryFormatData loadedBinary)
    elfHeader = EE.header elfData
    elfClass = EE.headerClass elfHeader
    staticSyms = symtabEntriesList $ EE.decodeHeaderSymtabLenient elfData
    dynSyms = symtabEntriesList $ EE.decodeHeaderDynsymLenient elfData

    symtabEntriesList :: Either EE.SymtabError (Maybe (EE.Symtab (G.RVWidth rv)))
                      -> [EE.SymtabEntry BS.ByteString (EE.ElfWordType (G.RVWidth rv))]
    symtabEntriesList symtab =
      case symtab of
        Left _ -> []
        Right Nothing -> []
        Right (Just st) -> F.toList (EE.symtabEntries st)

loadRiscvBinary :: forall m rv
                 . (X.MonadThrow m)
                => LC.LoadOptions
                -> EE.ElfHeaderInfo (G.RVWidth rv)
                -> m (MBL.LoadedBinary (MR.RISCV rv) (EE.ElfHeaderInfo (G.RVWidth rv)))
loadRiscvBinary lopts e =
  case EL.memoryForElf lopts e of
    Left err -> X.throwM (RISCVElfLoadError err)
    Right (mem, symbols, warnings, _) ->
      return MBL.LoadedBinary { MBL.memoryImage = mem
                              , MBL.memoryEndianness = MM.LittleEndian
                              , MBL.archBinaryData = ()
                              , MBL.binaryFormatData =
                                RISCVElfData { elf = e
                                             , memSymbols = symbols
                                             , symbolIndex = indexSymbols symbols
                                             }
                              , MBL.loadDiagnostics = warnings
                              , MBL.binaryRepr =
                                  case EE.headerClass (EE.header e) of
                                    EE.ELFCLASS32 -> MBL.Elf32Repr
                                    EE.ELFCLASS64 -> MBL.Elf64Repr
                              , MBL.originalBinary = e
                              , MBL.loadOptions = lopts
                              }

indexSymbols :: [EL.MemSymbol w] -> Map.Map (MM.MemAddr w) BS.ByteString
indexSymbols = F.foldl' doIndex Map.empty
  where
    doIndex m memSym =
      Map.insert (MM.segoffAddr (EL.memSymbolStart memSym)) (EL.memSymbolName memSym) m

data RISCVLoadException = RISCVElfLoadError String
                        | forall w. MissingSymbolFor (MM.MemAddr w)

deriving instance Show RISCVLoadException

instance X.Exception RISCVLoadException
