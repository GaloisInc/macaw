{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Macaw.BinaryLoader (
  BinaryLoader(..),
  LoadedBinary(..),
  BinaryRepr(..),
  addressWidth
  ) where

import qualified Control.Monad.Catch as X
import qualified Data.ElfEdit as E
import qualified Data.List.NonEmpty as NEL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Memory.LoadCommon as LC
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as NR
import           GHC.TypeNats


data BinaryRepr binFmt where
  Elf32Repr :: BinaryRepr (E.Elf 32)
  Elf64Repr :: BinaryRepr (E.Elf 64)

instance PC.TestEquality BinaryRepr where
  testEquality Elf32Repr Elf32Repr = Just PC.Refl
  testEquality Elf64Repr Elf64Repr = Just PC.Refl
  testEquality _ _ = Nothing

data LoadedBinary arch binFmt =
  LoadedBinary { memoryImage :: MM.Memory (MM.ArchAddrWidth arch)
               , archBinaryData :: ArchBinaryData arch binFmt
               , binaryFormatData :: BinaryFormatData arch binFmt
               , loadDiagnostics :: [Diagnostic arch binFmt]
               , binaryRepr :: BinaryRepr binFmt
               }

-- | A class for architecture and binary container independent binary loading
--
-- An instance is required for every arch/format pair, but the interface is more
-- accessible to callers than some alternatives.
--
-- n.b. many of the usage sites will need to express a constraint like:
--
-- > (BinaryAddrWidth binFmt ~ MC.ArchAddrWidth arch) =>
--
-- It would be nice to add that constraint directly to the class here,
-- but the macaw-loader family should only depend on macaw-base and
-- whatever loader (e.g. elf), and adding the above constraint
-- requires definitions from the macaw architecture specific modules
-- (e.g. macaw-ppc), creating a dependency cycle (because macaw-ppc
-- should be able to use macaw-loader-ppc). Ergo this constraint must
-- be expressed at the usage sites instead.

class BinaryLoader arch binFmt where
  -- | Architecture-specific information extracted from the binary
  type ArchBinaryData arch binFmt :: *
  -- | Information specific to the binary format that might be used later.
  type BinaryFormatData arch binFmt :: *
  type Diagnostic arch binFmt :: *
  -- | A loader for the given binary format at a caller-specified architecture
  loadBinary :: (X.MonadThrow m) => LC.LoadOptions -> binFmt -> m (LoadedBinary arch binFmt)
  -- | An architecture-specific function to return the entry points of a binary
  --
  -- This function is allowed (and encouraged) to find all possible entry points
  -- based on the metadata available in a binary.
  entryPoints :: (X.MonadThrow m) =>
                 LoadedBinary arch binFmt
              -> m (NEL.NonEmpty (MM.MemSegmentOff (MM.ArchAddrWidth arch)))


-- | Return a runtime representative of the pointer width of the architecture
addressWidth :: LoadedBinary arch binFmt -> NR.NatRepr (MM.ArchAddrWidth arch)
addressWidth = MM.memWidth . memoryImage
