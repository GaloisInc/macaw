{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.BinaryLoader.X86 (
  X86LoadException(..)
  ) where

import qualified Control.Monad.Catch as X
import qualified Data.ElfEdit as E
import qualified Data.Macaw.BinaryLoader as BL
import qualified Data.Macaw.Memory.ElfLoader as EL
import qualified Data.Macaw.Memory.LoadCommon as LC

import qualified Data.Macaw.X86 as MX

instance BL.BinaryLoader MX.X86_64 (E.Elf 64) where
  type ArchBinaryData MX.X86_64 = ()
  type BinaryFormatData (E.Elf 64) = EL.SectionIndexMap 64
  type Diagnostic (E.Elf 64) = EL.MemLoadWarning
  loadBinary = loadX86Binary

loadX86Binary :: (X.MonadThrow m)
              => LC.LoadOptions
              -> E.Elf 64
              -> m (BL.LoadedBinary MX.X86_64 (E.Elf 64))
loadX86Binary lopts e = do
  case EL.memoryForElf lopts e of
    Left err -> X.throwM (X86ElfLoadError err)
    Right (sim, mem, warnings) ->
      return BL.LoadedBinary { BL.memoryImage = mem
                             , BL.archBinaryData = ()
                             , BL.binaryFormatData = sim
                             , BL.loadDiagnostics = warnings
                             , BL.binaryRepr = BL.Elf64Repr
                             }

data X86LoadException = X86ElfLoadError String
                      deriving (Show)

instance X.Exception X86LoadException
