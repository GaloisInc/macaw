{-# LANGUAGE FlexibleContexts #-}
module Data.Macaw.PPC.TOC (
  TOC,
  toc,
  lookupTOC,
  lookupTOCAbs,
  entryPoints
  ) where

import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Word.Indexed as W

-- | The Table of Contents (TOC) of a PowerPC binary
--
-- Note that different ABIs and container formats store the TOC in different
-- places in the binary; this abstraction only concerns itself with the values
-- in the TOC and not their representation on disk.
newtype TOC ppc =
  TOC (M.Map (MC.MemAddr (MC.ArchAddrWidth ppc)) (W.W (MC.ArchAddrWidth ppc)))
  -- (MA.AbsValue (MC.ArchAddrWidth ppc) (MT.BVType (MC.ArchAddrWidth ppc))))

toc :: M.Map (MC.MemAddr (MC.ArchAddrWidth ppc)) (W.W (MC.ArchAddrWidth ppc)) -- (MA.AbsValue (MC.ArchAddrWidth ppc) (MT.BVType (MC.ArchAddrWidth ppc)))
    -> TOC ppc
toc = TOC

-- | Look up the value of the TOC base pointer for the function with the given address
--
-- A call
--
-- > lookupTOC toc addr
--
-- Returns the value of the TOC base pointer (i.e., the value in @r2@ when a
-- function begins executing) for the function whose entry point is at address
-- @addr@.
--
-- This variant returns a Macaw 'MA.AbsValue'
lookupTOCAbs :: (MC.MemWidth (MC.ArchAddrWidth ppc))
          => TOC ppc
          -> MC.ArchSegmentOff ppc
          -> Maybe (MA.AbsValue (MC.ArchAddrWidth ppc) (MT.BVType (MC.ArchAddrWidth ppc)))
lookupTOCAbs (TOC m) addr = (MA.FinSet . S.singleton . W.unW) <$> M.lookup (MC.relativeSegmentAddr addr) m

-- | Like 'lookupTOCAbs', but this variant returns a plain size-indexed word
lookupTOC :: (MC.MemWidth (MC.ArchAddrWidth ppc))
          => TOC ppc
          -> MC.ArchSegmentOff ppc
          -> Maybe (W.W (MC.ArchAddrWidth ppc))
lookupTOC (TOC m) addr = M.lookup (MC.relativeSegmentAddr addr) m

-- | Return the addresses of all of the functions present in the TOC
--
-- These addresses can be thought of as a root set of entry points in a binary
-- or library.
entryPoints :: TOC ppc -> [MC.MemAddr (MC.ArchAddrWidth ppc)]
entryPoints (TOC m) = M.keys m
