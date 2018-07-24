{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.PPC.Loader (
  PPCLoadException(..)
  ) where

import           GHC.TypeLits

import qualified Control.Monad.Catch as X
import qualified Data.ElfEdit as E
import qualified Data.List.NonEmpty as NEL
import qualified Data.Macaw.BinaryLoader as BL
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.ElfLoader as EL
import qualified Data.Macaw.Memory.LoadCommon as LC
import           Data.Macaw.PPC.PPCReg ()
import           Data.Maybe ( mapMaybe )
import           Data.Typeable ( Typeable )

import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64

import qualified Data.Macaw.PPC.BinaryFormat.ELF as BE
import qualified Data.Macaw.PPC.TOC as TOC

data PPCElfData w = PPCElfData { elf :: E.Elf w
                               , memSymbols :: [EL.MemSymbol w]
                               }

instance BL.BinaryLoader PPC32.PPC (E.Elf 32) where
  type ArchBinaryData PPC32.PPC (E.Elf 32) = TOC.TOC PPC32.PPC
  type BinaryFormatData PPC32.PPC (E.Elf 32) = PPCElfData 32
  type Diagnostic PPC32.PPC (E.Elf 32) = EL.MemLoadWarning
  loadBinary = loadPPCBinary BL.Elf32Repr
  entryPoints = ppcEntryPoints

instance BL.BinaryLoader PPC64.PPC (E.Elf 64) where
  type ArchBinaryData PPC64.PPC (E.Elf 64)  = TOC.TOC PPC64.PPC
  type BinaryFormatData PPC64.PPC (E.Elf 64) = PPCElfData 64
  type Diagnostic PPC64.PPC (E.Elf 64) = EL.MemLoadWarning
  loadBinary = loadPPCBinary BL.Elf64Repr
  entryPoints = ppcEntryPoints

ppcEntryPoints :: (X.MonadThrow m,
                   MC.MemWidth w,
                   Integral (E.ElfWordType w),
                   w ~ MC.ArchAddrWidth ppc,
                   BL.ArchBinaryData ppc (E.Elf w) ~ TOC.TOC ppc,
                   BL.BinaryFormatData ppc (E.Elf w) ~ PPCElfData w)
               => BL.LoadedBinary ppc (E.Elf w)
               -> m (NEL.NonEmpty (MC.MemSegmentOff w))
ppcEntryPoints loadedBinary = do
  entryAddr <- liftMemErr PPCElfMemoryError (MC.readAddr mem MC.BigEndian tocEntryAbsAddr)
  absEntryAddr <- liftMaybe (PPCInvalidAbsoluteAddress entryAddr) (MC.asSegmentOff mem entryAddr)
  let otherEntries = mapMaybe (MC.asSegmentOff mem) (TOC.entryPoints toc)
  return (absEntryAddr NEL.:| otherEntries)
  where
    tocEntryAddr = E.elfEntry (elf (BL.binaryFormatData loadedBinary))
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

loadPPCBinary :: (w ~ MC.ArchAddrWidth ppc,
                  X.MonadThrow m,
                  BL.ArchBinaryData ppc (E.Elf w) ~ TOC.TOC ppc,
                  BL.BinaryFormatData ppc (E.Elf w) ~ PPCElfData w,
                  BL.Diagnostic ppc (E.Elf w) ~ EL.MemLoadWarning,
                  MC.MemWidth w,
                  Typeable ppc,
                  KnownNat w)
              => BL.BinaryRepr (E.Elf w)
              -> LC.LoadOptions
              -> E.Elf (MC.ArchAddrWidth ppc)
              -> m (BL.LoadedBinary ppc (E.Elf (MC.ArchAddrWidth ppc)))
loadPPCBinary binRep lopts e = do
  case EL.memoryForElf lopts e of
    Left err -> X.throwM (PPCElfLoadError err)
    Right (mem, symbols, warnings, _) ->
      case BE.parseTOC e of
        Left err -> X.throwM (PPCTOCLoadError err)
        Right toc ->
          return BL.LoadedBinary { BL.memoryImage = mem
                                 , BL.archBinaryData = toc
                                 , BL.binaryFormatData =
                                   PPCElfData { elf = e
                                              , memSymbols = symbols
                                              }
                                 , BL.loadDiagnostics = warnings
                                 , BL.binaryRepr = binRep
                                 }

data PPCLoadException = PPCElfLoadError String
                      | PPCTOCLoadError X.SomeException
                      | forall w . (MC.MemWidth w) => PPCElfMemoryError (MC.MemoryError w)
                      | forall w . (MC.MemWidth w) => PPCInvalidAbsoluteAddress (MC.MemAddr w)

deriving instance Show PPCLoadException

instance X.Exception PPCLoadException
