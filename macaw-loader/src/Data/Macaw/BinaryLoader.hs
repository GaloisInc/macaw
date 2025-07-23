{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Data.Macaw.BinaryLoader (
  BinaryLoader(..),
  LoadedBinary(..),
  BinaryRepr(..),
  RawBin(..),
  addressWidth
  ) where

import qualified Control.Monad.Catch as X
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as E
import           Data.Kind ( Type )
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Memory.LoadCommon as LC
import qualified Data.Macaw.CFG.AssignRhs as MR
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as NR


newtype RawBin = RawBin BS.ByteString

data BinaryRepr binFmt where
  Elf32Repr :: BinaryRepr (E.ElfHeaderInfo 32)
  Elf64Repr :: BinaryRepr (E.ElfHeaderInfo 64)
  RawBinary :: BinaryRepr RawBin

instance PC.TestEquality BinaryRepr where
  testEquality Elf32Repr Elf32Repr = Just PC.Refl
  testEquality Elf64Repr Elf64Repr = Just PC.Refl
  testEquality RawBinary RawBinary = Just PC.Refl
  testEquality _ _ = Nothing

data LoadedBinary arch binFmt =
  LoadedBinary { memoryImage :: MM.Memory (MM.ArchAddrWidth arch)
               , memoryEndianness :: MM.Endianness
               , archBinaryData :: ArchBinaryData arch binFmt
               , binaryFormatData :: BinaryFormatData arch binFmt
               , loadDiagnostics :: [Diagnostic arch binFmt]
               , binaryRepr :: BinaryRepr binFmt
               , originalBinary :: binFmt
               , loadOptions :: LC.LoadOptions
               }

-- | A class for architecture and binary container independent binary loading
--
-- An instance is required for every arch/format pair, but the interface is more
-- accessible to callers than some alternatives.
--
-- n.b. The (MM.MemWidth (MR.ArchAddrWidth arch)) constraint enables
-- the LoadedBinary output type to functions by simply expressing
-- (BinaryLoader arch binFmt) as a constraint on those functions, but
-- many of the usage sites will still need to express a constraint
-- like:
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

class (MM.MemWidth (MR.ArchAddrWidth arch)) =>
      BinaryLoader arch binFmt where
  -- | Architecture-specific information extracted from the binary
  type ArchBinaryData arch binFmt :: Type
  -- | Information specific to the binary format that might be used later.
  type BinaryFormatData arch binFmt :: Type
  type Diagnostic arch binFmt :: Type

  -- | A loader for the given binary format at a caller-specified architecture
  loadBinary :: (X.MonadThrow m) => LC.LoadOptions -> binFmt -> m (LoadedBinary arch binFmt)
  -- | An architecture-specific function to return the entry points of a binary
  --
  -- This function is allowed (and encouraged) to find all possible
  -- entry points based on the metadata available in a binary.  Note
  -- that there is no guarantee of uniqueness in the results; in
  -- particular, an ELF file usually specifies an entryPoint address
  -- that is also an address in the symbol table, both of which are in
  -- the data returned by this function.
  entryPoints :: (X.MonadThrow m) =>
                 LoadedBinary arch binFmt
              -> m [MM.ArchSegmentOff arch]

  -- | Look up the symbol for the function or global at the given address, if any
  --
  -- This can fail if the address:
  --
  -- * Does not correspond to a global or function
  -- * Does not have an associated symbol
  --
  -- Symbols are 'BS.ByteString's because there is no encoding prescribed for them
  --
  -- This function is provided as 1) a container format independent method for
  -- accessing symbol information, and 2) to handle complex translations that
  -- may be required to interpret symbol addresses on a per-architecture basis.
  symbolFor :: (X.MonadThrow m)
            => LoadedBinary arch binFmt
            -> MM.MemAddr (MM.ArchAddrWidth arch)
            -> m BS.ByteString

-- | Return a runtime representative of the pointer width of the architecture
addressWidth :: LoadedBinary arch binFmt -> NR.NatRepr (MM.ArchAddrWidth arch)
addressWidth = MM.memWidth . memoryImage
