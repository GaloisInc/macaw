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
import qualified Data.Macaw.BinaryLoader as BL
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.ElfLoader as EL
import qualified Data.Macaw.Memory.LoadCommon as LC
import           Data.Macaw.PPC.PPCReg ()

import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64

import qualified Data.Macaw.PPC.BinaryFormat.ELF as BE
import qualified Data.Macaw.PPC.TOC as TOC

instance BL.BinaryLoader PPC32.PPC (E.Elf 32) where
  type ArchBinaryData PPC32.PPC = TOC.TOC PPC32.PPC
  type BinaryFormatData (E.Elf 32) = EL.SectionIndexMap 32
  type Diagnostic (E.Elf 32) = EL.MemLoadWarning
  loadBinary = loadPPCBinary BL.Elf32Repr

instance BL.BinaryLoader PPC64.PPC (E.Elf 64) where
  type ArchBinaryData PPC64.PPC = TOC.TOC PPC64.PPC
  type BinaryFormatData (E.Elf 64) = EL.SectionIndexMap 64
  type Diagnostic (E.Elf 64) = EL.MemLoadWarning
  loadBinary = loadPPCBinary BL.Elf64Repr

loadPPCBinary :: (w ~ MC.ArchAddrWidth ppc,
                  X.MonadThrow m,
                  BL.ArchBinaryData ppc ~ TOC.TOC ppc,
                  BL.BinaryFormatData (E.Elf w) ~ EL.SectionIndexMap w,
                  BL.Diagnostic (E.Elf w) ~ EL.MemLoadWarning,
                  MC.MemWidth w,
                  KnownNat w)
              => BL.BinaryRepr (E.Elf w)
              -> LC.LoadOptions
              -> E.Elf (MC.ArchAddrWidth ppc)
              -> m (BL.LoadedBinary ppc (E.Elf (MC.ArchAddrWidth ppc)))
loadPPCBinary binRep lopts e = do
  case EL.memoryForElf lopts e of
    Left err -> X.throwM (PPCElfLoadError err)
    Right (sim, mem, warnings) ->
      case BE.parseTOC e of
        Left err -> X.throwM (PPCTOCLoadError err)
        Right toc ->
          return BL.LoadedBinary { BL.memoryImage = mem
                                 , BL.archBinaryData = toc
                                 , BL.binaryFormatData = sim
                                 , BL.loadDiagnostics = warnings
                                 , BL.binaryRepr = binRep
                                 }

data PPCLoadException = PPCElfLoadError String
                      | PPCTOCLoadError X.SomeException
                      deriving (Show)

instance X.Exception PPCLoadException
