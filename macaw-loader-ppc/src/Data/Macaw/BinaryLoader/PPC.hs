{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Macaw.BinaryLoader.PPC
  ( PPCLoadException(..)
  , HasTOC(..)
  )
where

import qualified Control.Monad.Catch as X
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as E
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as NEL
import qualified Data.Macaw.BinaryLoader as BL
import qualified Data.Macaw.BinaryLoader.PPC.ELF as BE
import qualified Data.Macaw.BinaryLoader.PPC.TOC as TOC
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.ElfLoader as EL
import qualified Data.Macaw.Memory.LoadCommon as LC
import qualified Data.Map.Strict as Map
import           Data.Maybe ( mapMaybe )
import           Data.Typeable ( Typeable )
import           GHC.TypeLits
import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64

class HasTOC arch binFmt where
  getTOC :: BL.LoadedBinary arch binFmt -> TOC.TOC (MC.ArchAddrWidth arch)

data PPCElfData w = PPCElfData { elf :: E.ElfHeaderInfo w
                               , memSymbols :: [EL.MemSymbol w]
                               , symbolIndex :: Map.Map (MC.MemAddr w) BS.ByteString
                               }

-- NOTE: This funny constraint is necessary because we don't have access to the
-- PPCReg type here.  If we could import that type and get its associated
-- instances, this information would be apparent to the compiler, but we can't
-- import it because it is in a package we can't depend on.  Anywhere we use
-- this instance, the compiler will ensure that the assertion is actually true.
instance (MC.ArchAddrWidth PPC32.PPC ~ 32) => BL.BinaryLoader PPC32.PPC (E.ElfHeaderInfo 32) where
  type ArchBinaryData PPC32.PPC (E.ElfHeaderInfo 32) = TOC.TOC 32
  type BinaryFormatData PPC32.PPC (E.ElfHeaderInfo 32) = PPCElfData 32
  type Diagnostic PPC32.PPC (E.ElfHeaderInfo 32) = EL.MemLoadWarning
  loadBinary = loadPPCBinary BL.Elf32Repr
  entryPoints = ppcEntryPoints
  symbolFor = ppcLookupSymbol

instance (MC.ArchAddrWidth PPC32.PPC ~ 32) => HasTOC PPC32.PPC (E.ElfHeaderInfo 32) where
  getTOC = BL.archBinaryData

instance (MC.ArchAddrWidth PPC64.PPC ~ 64) => BL.BinaryLoader PPC64.PPC (E.ElfHeaderInfo 64) where
  type ArchBinaryData PPC64.PPC (E.ElfHeaderInfo 64)  = TOC.TOC 64
  type BinaryFormatData PPC64.PPC (E.ElfHeaderInfo 64) = PPCElfData 64
  type Diagnostic PPC64.PPC (E.ElfHeaderInfo 64) = EL.MemLoadWarning
  loadBinary = loadPPCBinary BL.Elf64Repr
  entryPoints = ppcEntryPoints
  symbolFor = ppcLookupSymbol

instance (MC.ArchAddrWidth PPC64.PPC ~ 64) => HasTOC PPC64.PPC (E.ElfHeaderInfo 64) where
  getTOC = BL.archBinaryData

ppcLookupSymbol :: (X.MonadThrow m, MC.MemWidth w, BL.BinaryFormatData arch binFmt ~ PPCElfData w)
                => BL.LoadedBinary arch binFmt
                -> MC.MemAddr w
                -> m BS.ByteString
ppcLookupSymbol loadedBinary funcAddr =
  case Map.lookup funcAddr (symbolIndex (BL.binaryFormatData loadedBinary)) of
    Nothing -> X.throwM (PPCNoFunctionAddressForTOCEntry funcAddr)
    Just sym -> return sym

ppcEntryPoints :: (X.MonadThrow m,
                   MC.MemWidth w,
                   Integral (E.ElfWordType w),
                   MC.ArchAddrWidth ppc ~ w,
                   BL.ArchBinaryData ppc (E.ElfHeaderInfo w) ~ TOC.TOC w,
                   BL.BinaryFormatData ppc (E.ElfHeaderInfo w) ~ PPCElfData w)
               => BL.LoadedBinary ppc (E.ElfHeaderInfo w)
               -> m (NEL.NonEmpty (MC.MemSegmentOff w))
ppcEntryPoints loadedBinary = do
  entryAddr <- liftMemErr PPCElfMemoryError
               (MC.readAddr mem (BL.memoryEndianness loadedBinary) tocEntryAbsAddr)
  absEntryAddr <- liftMaybe (PPCInvalidAbsoluteAddress entryAddr) (MC.asSegmentOff mem entryAddr)
  let otherEntries = mapMaybe (MC.asSegmentOff mem) (TOC.entryPoints toc)
  return (absEntryAddr NEL.:| otherEntries)
  where
    tocEntryAddr = E.headerEntry $ E.header (elf (BL.binaryFormatData loadedBinary))
    tocEntryAbsAddr :: EL.MemWidth w => MC.MemAddr w
    tocEntryAbsAddr = MC.absoluteAddr (MC.memWord (fromIntegral tocEntryAddr))
    toc = BL.archBinaryData loadedBinary
    mem = BL.memoryImage loadedBinary

liftMaybe :: (X.Exception e, X.MonadThrow m) => e -> Maybe a -> m a
liftMaybe exn a =
  case a of
    Nothing -> X.throwM exn
    Just res -> return res

liftMemErr :: (X.Exception e, X.MonadThrow m) => (t -> e) -> Either t a -> m a
liftMemErr exn a =
  case a of
    Left err -> X.throwM (exn err)
    Right res -> return res

loadPPCBinary :: (X.MonadThrow m,
                  BL.ArchBinaryData ppc (E.ElfHeaderInfo w) ~ TOC.TOC w,
                  BL.BinaryFormatData ppc (E.ElfHeaderInfo w) ~ PPCElfData w,
                  MC.ArchAddrWidth ppc ~ w,
                  Integral (E.ElfWordType w),
                  BL.Diagnostic ppc (E.ElfHeaderInfo w) ~ EL.MemLoadWarning,
                  MC.MemWidth w,
                  Typeable w,
                  KnownNat w)
              => BL.BinaryRepr (E.ElfHeaderInfo w)
              -> LC.LoadOptions
              -> E.ElfHeaderInfo w
              -> m (BL.LoadedBinary ppc (E.ElfHeaderInfo w))
loadPPCBinary binRep lopts e = do
  case EL.memoryForElf lopts e of
    Left err -> X.throwM (PPCElfLoadError err)
    Right (mem, symbols, warnings, _) ->
      case BE.parseTOC e of
        Left err -> X.throwM (PPCTOCLoadError err)
        Right toc ->
          return BL.LoadedBinary { BL.memoryImage = mem
                                 , BL.memoryEndianness = MC.BigEndian
                                 , BL.archBinaryData = toc
                                 , BL.binaryFormatData =
                                   PPCElfData { elf = e
                                              , memSymbols = symbols
                                              , symbolIndex = indexSymbols toc symbols
                                              }
                                 , BL.loadDiagnostics = warnings
                                 , BL.binaryRepr = binRep
                                 }

indexSymbols :: (Foldable t)
             => TOC.TOC w
             -> t (EL.MemSymbol w)
             -> Map.Map (EL.MemAddr w) BS.ByteString
indexSymbols toc = F.foldl' doIndex Map.empty
  where
    doIndex m memSym =
      case TOC.mapTOCEntryAddress toc (MC.segoffAddr (EL.memSymbolStart memSym)) of
        Nothing -> m
        Just funcAddr -> Map.insert funcAddr (EL.memSymbolName memSym) m

data PPCLoadException = PPCElfLoadError String
                      | PPCTOCLoadError X.SomeException
                      | forall w . (MC.MemWidth w) => PPCElfMemoryError (MC.MemoryError w)
                      | forall w . (MC.MemWidth w) => PPCInvalidAbsoluteAddress (MC.MemAddr w)
                      | forall w . (MC.MemWidth w) => PPCNoFunctionAddressForTOCEntry (MC.MemAddr w)

deriving instance Show PPCLoadException

instance X.Exception PPCLoadException
