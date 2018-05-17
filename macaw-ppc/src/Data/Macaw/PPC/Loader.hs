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

import qualified Control.Exception as X
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
  loadBinary = loadPPCBinary

instance BL.BinaryLoader PPC64.PPC (E.Elf 64) where
  type ArchBinaryData PPC64.PPC = TOC.TOC PPC64.PPC
  type BinaryFormatData (E.Elf 64) = EL.SectionIndexMap 64
  type Diagnostic (E.Elf 64) = EL.MemLoadWarning
  loadBinary = loadPPCBinary

loadPPCBinary :: (w ~ MC.ArchAddrWidth ppc,
                  BL.ArchBinaryData ppc ~ TOC.TOC ppc,
                  BL.BinaryFormatData (E.Elf w) ~ EL.SectionIndexMap w,
                  BL.Diagnostic (E.Elf w) ~ EL.MemLoadWarning,
                  MC.MemWidth w,
                  KnownNat w)
              => LC.LoadOptions
              -> E.Elf (MC.ArchAddrWidth ppc)
              -> IO (BL.LoadedBinary ppc (E.Elf (MC.ArchAddrWidth ppc)))
loadPPCBinary lopts e = do
  case EL.memoryForElf lopts e of
    Left err -> X.throwIO (PPCElfLoadError err)
    Right (sim, mem, warnings) ->
      case BE.parseTOC e of
        Left err -> X.throwIO (PPCTOCLoadError err)
        Right toc ->
          return BL.LoadedBinary { BL.memoryImage = mem
                                 , BL.archBinaryData = toc
                                 , BL.binaryFormatData = sim
                                 , BL.loadDiagnostics = warnings
                                 }

data PPCLoadException = PPCElfLoadError String
                      | PPCTOCLoadError X.SomeException
                      deriving (Show)

instance X.Exception PPCLoadException
