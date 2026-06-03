{-|
Copyright   : (c) Galois Inc, 2026
Maintainer  : Langston Barrett <langston@galois.com>

Read the @.llvm_jump_table_sizes@ section emitted by Clang/LLVM (>= 20)
when compiled with @-mllvm -emit-jump-table-sizes-section@.

The section consists of a sequence of fixed-size entries; each entry is two
target-pointer-sized words written in target endianness:

  * the address of the jump table, and
  * the number of basic-block targets in that jump table.

See @SHT_LLVM_JT_SIZES@ in the LLVM @ELF.h@ header and
<https://llvm.org/docs/Extensions.html>.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Macaw.Memory.LLVMJumpTableSizes
  ( sectionName
  , JumpTableSize(..)
  , SectionSizeError(..)
  , UnresolvableAddress(..)
  , parseLLVMJumpTableSizes
  , llvmJumpTableSizesFromElf
  ) where

import qualified Data.ByteString as BS
import qualified Data.ElfEdit as Elf
import qualified Data.Foldable as F
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Numeric (showHex)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.String as PP

import           Data.Macaw.Memory

-- | The section byte count was not a multiple of the entry size.
data SectionSizeError
  = SectionSizeError
      Int  -- ^ actual section size in bytes
      Int  -- ^ required entry size in bytes
  deriving Eq

instance PP.Pretty SectionSizeError where
  pretty = \case
    SectionSizeError total entry ->
      PP.pretty (show sectionName) PP.<+> "section size" PP.<+> PP.pretty total
        PP.<+> "is not a multiple of entry size" PP.<+> PP.pretty entry

instance Show SectionSizeError where
  show = PP.renderString . PP.layoutPretty PP.defaultLayoutOptions . PP.pretty

-- | An entry's jump-table address could not be resolved in the 'Memory'.
newtype UnresolvableAddress w = UnresolvableAddress (MemWord w)
  deriving Eq

instance MemWidth w => PP.Pretty (UnresolvableAddress w) where
  pretty = \case
    UnresolvableAddress addr ->
      PP.pretty (show sectionName) PP.<> ": could not resolve address 0x"
        PP.<> PP.pretty (showHex (memWordValue addr) "")

instance MemWidth w => Show (UnresolvableAddress w) where
  show = PP.renderString . PP.layoutPretty PP.defaultLayoutOptions . PP.pretty

-- | The number of basic-block targets (entries) in a jump table, as recorded
-- in a Clang\/LLVM @.llvm_jump_table_sizes@ section.
--
-- The type parameter @w@ is the target address width.
newtype JumpTableSize w = JumpTableSize { getJumpTableSize :: MemWord w }
  deriving (Eq, Show)

-- | The ELF section name emitted by LLVM.
sectionName :: BS.ByteString
sectionName = ".llvm_jump_table_sizes"

-- | Parse the raw bytes of a @.llvm_jump_table_sizes@ section.
--
-- Each entry is two pointer-sized words: @(address, entry_count)@. The
-- bytestring length must be an exact multiple of @2 * pointer_size@; otherwise
-- a 'Left' is returned.
parseLLVMJumpTableSizes
  :: forall w
  .  AddrWidthRepr w
  -> Endianness
  -> BS.ByteString
  -> Either SectionSizeError [(MemWord w, JumpTableSize w)]
parseLLVMJumpTableSizes wRepr end bs0 = addrWidthClass wRepr $
  let ptrBytes = fromIntegral (addrWidthReprByteCount wRepr) :: Int
      entryBytes = 2 * ptrBytes
      totalLen = BS.length bs0
      readWord bs = case wRepr of
        Addr32 -> fromIntegral (bsWord32 end bs)
        Addr64 -> bsWord64 end bs
      go :: MemWidth w => BS.ByteString -> [(MemWord w, JumpTableSize w)]
      go bs
        | BS.null bs = []
        | otherwise =
            let (addrBs, rest1) = BS.splitAt ptrBytes bs
                (cntBs, rest2) = BS.splitAt ptrBytes rest1
            in (memWord (readWord addrBs), JumpTableSize (memWord (readWord cntBs))) : go rest2
  in if totalLen `mod` entryBytes /= 0
       then Left (SectionSizeError totalLen entryBytes)
       else Right (go bs0)

-- | Read the @.llvm_jump_table_sizes@ section out of an ELF binary, parse
-- it, and resolve each address against the provided 'Memory'.
--
-- Returns a parse error if the section is malformed, otherwise a list of
-- per-entry warnings (one per unresolvable address) along with a map from
-- resolved jump-table base addresses to entry counts.
--
-- If the section is absent the result is @Right ([], Map.empty)@.
llvmJumpTableSizesFromElf
  :: forall w
  .  Elf.ElfHeaderInfo w
  -> Memory w
  -> Either SectionSizeError ([UnresolvableAddress w], Map (MemSegmentOff w) (JumpTableSize w))
llvmJumpTableSizesFromElf ehi mem =
  let end = case Elf.headerData (Elf.header ehi) of
              Elf.ELFDATA2LSB -> LittleEndian
              Elf.ELFDATA2MSB -> BigEndian
      sectionBytes =
        [ Elf.elfSectionData sec
        | (_, sec) <- F.toList (Elf.headerSections ehi)
        , Elf.elfSectionName sec == sectionName
        ]
      wRepr :: AddrWidthRepr w
      wRepr = case Elf.headerClass (Elf.header ehi) of
                Elf.ELFCLASS32 -> Addr32
                Elf.ELFCLASS64 -> Addr64
  in addrWidthClass wRepr $ case sectionBytes of
       [] -> Right ([], Map.empty)
       bs : _ -> resolveEntries mem <$> parseLLVMJumpTableSizes wRepr end bs

resolveEntries
  :: MemWidth w
  => Memory w
  -> [(MemWord w, JumpTableSize w)]
  -> ([UnresolvableAddress w], Map (MemSegmentOff w) (JumpTableSize w))
resolveEntries mem = F.foldl' step ([], Map.empty)
  where
    step (errs, m) (addr, cnt) =
      case resolveAbsoluteAddr mem addr of
        Nothing -> (UnresolvableAddress addr : errs, m)
        Just segOff -> (errs, Map.insert segOff cnt m)
