{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Data.Macaw.BinaryLoader.PPC.TOC
  ( TOC
  , toc
  , lookupTOC
  , lookupTOCAbs
  , entryPoints
  , TOCException(..)
  )
where

import qualified Control.Monad.Catch as X
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as MT
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Typeable ( Typeable )
import qualified Data.Word.Indexed as W

data TOCException w = MissingTOCEntry (MM.MemSegmentOff w)
                      | MissingTOCSection String
                      | TOCParseError String

deriving instance (MM.MemWidth w) => Show (TOCException w)

instance (MM.MemWidth w, Typeable w) => X.Exception (TOCException w)

-- | The Table of Contents (TOC) of a PowerPC binary
--
-- Note that different ABIs and container formats store the TOC in different
-- places in the binary; this abstraction only concerns itself with the values
-- in the TOC and not their representation on disk.
newtype TOC w = TOC (M.Map (MM.MemAddr w) (W.W w))

toc :: M.Map (MM.MemAddr w) (W.W w) -> TOC w
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
lookupTOC (TOC m) addr = M.lookup (MM.segoffAddr addr) m

-- | Return the addresses of all of the functions present in the TOC
--
-- These addresses can be thought of as a root set of entry points in a binary
-- or library.
-- entryPoints :: TOC ppc -> [MC.MemAddr (MC.ArchAddrWidth ppc)]
entryPoints :: TOC w -> [MM.MemAddr w]
entryPoints (TOC m) = M.keys m
