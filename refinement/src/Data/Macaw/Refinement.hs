{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Refinement
  ( -- * Simple entry points
    cfgFromAddrsAndState
  , cfgFromAddrs
    -- * Entry points with extra diagnostic info
  , cfgFromAddrsAndStateWith
  , cfgFromAddrsWith
  , RefinementFindings
  , RefinementInfo(..)
  , RefinementLog(..)
    -- * Configuration
  , RSE.defaultRefinementContext
  , RSE.RefinementContext
  , MRS.Solver(..)
  , RSE.RefinementConfig(..)
  , RSE.defaultRefinementConfig
  -- * Low-level interface
  , refineDiscovery
  )
where

import           GHC.TypeLits

import qualified Control.Monad.Catch as X
import qualified Control.Monad.IO.Unlift as MU
import qualified Data.Macaw.Architecture.Info as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import           Data.Macaw.Discovery.State
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.LLVM.MemModel as LLVM
import qualified Lumberjack as LJ

import           Data.Macaw.Refinement.Logging ( RefinementLog(..) )
import qualified Data.Macaw.Refinement.Solver as MRS
import qualified Data.Macaw.Refinement.SymbolicExecution as RSE
import           Data.Macaw.Refinement.Target
import           Data.Macaw.Refinement.UnknownTransfer

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
     , MU.MonadUnliftIO m
     , LJ.HasLog (RefinementLog arch) m
     , X.MonadThrow m
     , ?memOpts :: LLVM.MemOptions
     )
  => RSE.RefinementContext arch
  -> MD.DiscoveryState arch
  -> [MC.ArchSegmentOff arch]
  -- ^ Initial function entry points.
  -> [(MC.ArchSegmentOff arch, MC.ArchSegmentOff arch)]
  -- ^ Function entry points in memory to be explored
  -- after exploring function entry points.
  --
  -- Each entry contains an address and the value stored in it.
  -> m (DiscoveryState arch)
cfgFromAddrsAndState context initial_state init_addrs mem_words =
  fst <$> cfgFromAddrsAndStateWith context initial_state init_addrs mem_words

cfgFromAddrsAndStateWith
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MU.MonadUnliftIO m
     , LJ.HasLog (RefinementLog arch) m
     , X.MonadThrow m
     , ?memOpts :: LLVM.MemOptions
     )
  => RSE.RefinementContext arch
  -> MD.DiscoveryState arch
  -> [MC.ArchSegmentOff arch]
  -- ^ Initial function entry points.
  -> [(MC.ArchSegmentOff arch, MC.ArchSegmentOff arch)]
  -- ^ Function entry points in memory to be explored
  -- after exploring function entry points.
  --
  -- Each entry contains an address and the value stored in it.
  -> m (DiscoveryState arch, RefinementInfo arch)
cfgFromAddrsAndStateWith context initial_state init_addrs mem_words =
  go (MD.cfgFromAddrsAndState initial_state init_addrs mem_words) mempty
  where
    go s0 findings = do
      (s1, newFindings) <- refineDiscovery context findings s0
      case findings == newFindings of
        True -> return (s1, findingsInfo newFindings)
        False -> go s1 newFindings


-- | Construct an empty discovery state and populate it by exploring
-- from a given set of function entry points.  This can be used as an
-- alternate entry point from the same named function in
-- Data.Macaw.Discovery.
cfgFromAddrs
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MU.MonadUnliftIO m
     , LJ.HasLog (RefinementLog arch) m
     , X.MonadThrow m
     , ?memOpts :: LLVM.MemOptions
     )
  => RSE.RefinementContext arch
  -> MA.ArchitectureInfo arch
  -- ^ Architecture-specific information needed for doing
  -- control-flow exploration.
  -> MM.Memory (MC.ArchAddrWidth arch)
  -- ^ Memory to use when decoding instructions.
  -> AddrSymMap (MC.ArchAddrWidth arch)
  -- ^ Map from addresses to the associated symbol name.
  -> [MC.ArchSegmentOff arch]
  -- ^ Initial function entry points.
  -> [(MC.ArchSegmentOff arch, MC.ArchSegmentOff arch)]
  -- ^ Function entry points in memory to be explored
  -- after exploring function entry points.
  --
  -- Each entry contains an address and the value stored in it.
  -> m (DiscoveryState arch)
cfgFromAddrs context ainfo mem addrSymMap =
  cfgFromAddrsAndState context (emptyDiscoveryState mem addrSymMap ainfo)

cfgFromAddrsWith
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MU.MonadUnliftIO m
     , LJ.HasLog (RefinementLog arch) m
     , X.MonadThrow m
     , ?memOpts :: LLVM.MemOptions
     )
  => RSE.RefinementContext arch
  -> MA.ArchitectureInfo arch
  -- ^ Architecture-specific information needed for doing
  -- control-flow exploration.
  -> MM.Memory (MC.ArchAddrWidth arch)
  -- ^ Memory to use when decoding instructions.
  -> AddrSymMap (MC.ArchAddrWidth arch)
  -- ^ Map from addresses to the associated symbol name.
  -> [MC.ArchSegmentOff arch]
  -- ^ Initial function entry points.
  -> [(MC.ArchSegmentOff arch, MC.ArchSegmentOff arch)]
  -- ^ Function entry points in memory to be explored
  -- after exploring function entry points.
  --
  -- Each entry contains an address and the value stored in it.
  -> m (DiscoveryState arch, RefinementInfo arch)
cfgFromAddrsWith context ainfo mem addrSymMap =
  cfgFromAddrsAndStateWith context (emptyDiscoveryState mem addrSymMap ainfo)


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
     , MU.MonadUnliftIO m
     , LJ.HasLog (RefinementLog arch) m
     , X.MonadThrow m
     , ?memOpts :: LLVM.MemOptions
     )
  => RSE.RefinementContext arch
  -> RefinementFindings arch
  -> DiscoveryState arch
  -> m (DiscoveryState arch, RefinementFindings arch)
refineDiscovery context oldFindings =
  symbolicUnkTransferRefinement context oldFindings . symbolicTargetRefinement
