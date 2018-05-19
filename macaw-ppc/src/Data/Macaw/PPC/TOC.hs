{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Macaw.PPC.TOC (
  TOC,
  toc,
  lookupTOC,
  lookupTOCAbs,
  entryPoints,
  TOCException(..)
  ) where

import qualified Control.Monad.Catch as X
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Typeable ( Typeable )
import qualified Data.Word.Indexed as W

data TOCException ppc = MissingTOCEntry (MC.ArchSegmentOff ppc)
                      | MissingTOCSection String
                      | TOCParseError String

deriving instance (MC.MemWidth (MC.ArchAddrWidth ppc)) => Show (TOCException ppc)

instance (Typeable ppc, MC.MemWidth (MC.ArchAddrWidth ppc)) => X.Exception (TOCException ppc)

-- | The Table of Contents (TOC) of a PowerPC binary
--
-- Note that different ABIs and container formats store the TOC in different
-- places in the binary; this abstraction only concerns itself with the values
-- in the TOC and not their representation on disk.
newtype TOC ppc =
  TOC (M.Map (MC.MemAddr (MC.ArchAddrWidth ppc)) (W.W (MC.ArchAddrWidth ppc)))

toc :: M.Map (MC.MemAddr (MC.ArchAddrWidth ppc)) (W.W (MC.ArchAddrWidth ppc))
    -> TOC ppc
toc = TOC

-- | A variant of 'lookupTOC' that returns a macaw 'MA.AbsValue'
lookupTOCAbs :: (MC.MemWidth (MC.ArchAddrWidth ppc), X.MonadThrow m, Typeable ppc)
             => TOC ppc
             -> MC.ArchSegmentOff ppc
             -> m (MA.AbsValue (MC.ArchAddrWidth ppc) (MT.BVType (MC.ArchAddrWidth ppc)))
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
lookupTOC :: forall ppc m
           . (MC.MemWidth (MC.ArchAddrWidth ppc), X.MonadThrow m, Typeable ppc)
          => TOC ppc
          -> MC.ArchSegmentOff ppc
          -> m (W.W (MC.ArchAddrWidth ppc))
lookupTOC (TOC m) addr =
  case M.lookup (MC.relativeSegmentAddr addr) m of
    Nothing ->
      let x :: TOCException ppc
          x = MissingTOCEntry addr
      in X.throwM x
    Just entry -> return entry

-- | Return the addresses of all of the functions present in the TOC
--
-- These addresses can be thought of as a root set of entry points in a binary
-- or library.
entryPoints :: TOC ppc -> [MC.MemAddr (MC.ArchAddrWidth ppc)]
entryPoints (TOC m) = M.keys m
