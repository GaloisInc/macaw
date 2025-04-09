{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Data.Macaw.BinaryLoader.PPC.TOC
  ( TOC
  , toc
  , lookupTOC
  , lookupTOCAbs
  , entryPoints
  , mapTOCEntryAddress
  , TOCException(..)
  )
where

import qualified Control.Monad.Catch as X
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as MT
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Word.Indexed as W

data TOCException w = MissingTOCEntry (MM.MemSegmentOff w)
                      | MissingTOCSection String
                      | TOCParseError String

deriving instance (MM.MemWidth w) => Show (TOCException w)

instance (MM.MemWidth w, MT.KnownNat w) => X.Exception (TOCException w)

-- | The Table of Contents (TOC) of a PowerPC binary
--
-- Note that different ABIs and container formats store the TOC in different
-- places in the binary; this abstraction only concerns itself with the values
-- in the TOC and not their representation on disk.
data TOC w = TOC { funcTOCPtrValues :: M.Map (MM.MemAddr w) (W.W w)
                 -- ^ The map from actual function address to the value of the
                 -- TOC pointer at the start of that function (NOTE: This value
                 -- is almost always not the same as the address of the TOC
                 -- entry for the function).
                 , symbolAddressMapping :: M.Map (MM.MemAddr w) (MM.MemAddr w)
                 -- ^ The mapping from symbol table addresses (which point to
                 -- TOC entries) to the addresses of the actual corresponding
                 -- functions in the .text section
                 }

toc :: M.Map (MM.MemAddr w) (W.W w) -> M.Map (MM.MemAddr w) (MM.MemAddr w) -> TOC w
toc = TOC

-- | A variant of 'lookupTOC' that returns a macaw 'MA.AbsValue'
lookupTOCAbs :: MM.MemWidth w
             => TOC w
             -> MM.MemSegmentOff w
             -> Maybe (MA.AbsValue w (MT.BVType w))
lookupTOCAbs t addr = toAbsVal <$> lookupTOC t addr
  where
    toAbsVal = MA.FinSet . S.singleton . W.unW

-- | Look up the value of the TOC base pointer for the function with the given address
--
-- A call
--
-- > lookupTOC toc addr
--
-- Returns the value of the TOC base pointer (i.e., the value in @r2@ when a
-- function begins executing) for the function whose entry point is at address
-- @addr@.
lookupTOC :: forall w . (MM.MemWidth w) => TOC w -> MM.MemSegmentOff w -> Maybe (W.W w)
lookupTOC t addr = M.lookup (MM.segoffAddr addr) (funcTOCPtrValues t)

-- | Return the addresses of all of the functions present in the TOC
--
-- These addresses can be thought of as a root set of entry points in a binary
-- or library.
-- entryPoints :: TOC ppc -> [MC.MemAddr (MC.ArchAddrWidth ppc)]
entryPoints :: TOC w -> [MM.MemAddr w]
entryPoints t = M.keys (funcTOCPtrValues t)

mapTOCEntryAddress :: TOC w -> MM.MemAddr w -> Maybe (MM.MemAddr w)
mapTOCEntryAddress t a = M.lookup a (symbolAddressMapping t)
