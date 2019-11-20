{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Refinement
  ( cfgFromAddrsAndState
  , cfgFromAddrs
  , refineDiscovery
  , RSE.defaultRefinementContext
  , RSE.RefinementContext
  , RSE.Refinement
  )
where

import           GHC.TypeLits

import           Control.Lens
import           Control.Monad.IO.Class (MonadIO)
import qualified Data.Macaw.Architecture.Info as MA
import           Data.Macaw.CFG.AssignRhs
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import           Data.Macaw.Discovery.State
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Symbolic as MS
import           Data.Macaw.Refinement.Target
import           Data.Macaw.Refinement.UnknownTransfer
import qualified Data.Macaw.Refinement.SymbolicExecution as RSE

----------------------------------------------------------------------
-- * Discovery Entrypoints
--
-- These entrypoints match those of Data.Macaw.Discovery and can be
-- used in place of the calls to Discovery because internally they
-- will call discovery and then perform the additional refinements.

-- | Expand an initial discovery state by exploring from a given set
-- of function entry points.  This entry point can be used as an
-- alternative to the same named function in Data.Macaw.Discovery.
cfgFromAddrsAndState
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MonadIO m
     , RSE.Refinement t solver fp
     )
  => RSE.RefinementContext arch t solver fp
  -> MD.DiscoveryState arch
  -> [ArchSegmentOff arch]
  -- ^ Initial function entry points.
  -> [(ArchSegmentOff arch, ArchSegmentOff arch)]
  -- ^ Function entry points in memory to be explored
  -- after exploring function entry points.
  --
  -- Each entry contains an address and the value stored in it.
  -> m (DiscoveryState arch)
cfgFromAddrsAndState context initial_state init_addrs mem_words =
  MD.cfgFromAddrsAndState initial_state init_addrs mem_words
    & refineDiscovery context

-- | Construct an empty discovery state and populate it by exploring
-- from a given set of function entry points.  This can be used as an
-- alternate entry point from the same named function in
-- Data.Macaw.Discovery.
cfgFromAddrs
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MonadIO m
     , RSE.Refinement t solver fp
     )
  => RSE.RefinementContext arch t solver fp
  -> MA.ArchitectureInfo arch
  -- ^ Architecture-specific information needed for doing
  -- control-flow exploration.
  -> MM.Memory (ArchAddrWidth arch)
  -- ^ Memory to use when decoding instructions.
  -> AddrSymMap (ArchAddrWidth arch)
  -- ^ Map from addresses to the associated symbol name.
  -> [ArchSegmentOff arch]
  -- ^ Initial function entry points.
  -> [(ArchSegmentOff arch, ArchSegmentOff arch)]
  -- ^ Function entry points in memory to be explored
  -- after exploring function entry points.
  --
  -- Each entry contains an address and the value stored in it.
  -> m (DiscoveryState arch)
cfgFromAddrs context ainfo mem addrSymMap =
  cfgFromAddrsAndState context (emptyDiscoveryState mem addrSymMap ainfo)


----------------------------------------------------------------------
-- * Refinement process
--
-- This is the main entrypoint to refining the discovered information.
-- This is invoked automatically by the Discovery entrypoints, or if
-- discovery has already yielded a 'DiscoveryState' result, that
-- result can be refined by passing it to the 'refineDiscovery'
-- entrypoint.

-- | Refine an existing discovery state by using a symbolic backend to
-- perform additional discovery for incomplete blocks.
refineDiscovery
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MonadIO m
     , RSE.Refinement t solver fp
     )
  => RSE.RefinementContext arch t solver fp
  -> DiscoveryState arch
  -> m (DiscoveryState arch)
refineDiscovery context =
  symbolicUnkTransferRefinement context . symbolicTargetRefinement
