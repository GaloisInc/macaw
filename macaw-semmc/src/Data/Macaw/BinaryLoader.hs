{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Macaw.BinaryLoader (
  BinaryLoader(..),
  LoadedBinary(..),
  BinaryRepr(..),
  addressWidth
  ) where

import qualified Control.Monad.Catch as X
import qualified Data.ElfEdit as E
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.LoadCommon as LC
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as NR

data BinaryRepr binFmt where
  Elf32Repr :: BinaryRepr (E.Elf 32)
  Elf64Repr :: BinaryRepr (E.Elf 64)

instance PC.TestEquality BinaryRepr where
  testEquality Elf32Repr Elf32Repr = Just PC.Refl
  testEquality Elf64Repr Elf64Repr = Just PC.Refl
  testEquality _ _ = Nothing

data LoadedBinary arch binFmt =
  LoadedBinary { memoryImage :: MC.Memory (MC.ArchAddrWidth arch)
               , archBinaryData :: ArchBinaryData arch
               , binaryFormatData :: BinaryFormatData binFmt
               , loadDiagnostics :: [Diagnostic binFmt]
               , binaryRepr :: BinaryRepr binFmt
               }

class BinaryLoader arch binFmt where
  type ArchBinaryData arch :: *
  type BinaryFormatData binFmt :: *
  type Diagnostic binFmt :: *
  loadBinary :: (X.MonadThrow m) => LC.LoadOptions -> binFmt -> m (LoadedBinary arch binFmt)

addressWidth :: LoadedBinary arch binFmt -> NR.NatRepr (MC.ArchAddrWidth arch)
addressWidth = MC.memWidth . memoryImage
