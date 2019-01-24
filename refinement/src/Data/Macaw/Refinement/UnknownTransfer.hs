-- | This module uses symbolic evaluation to refine the discovered CFG
-- and resolve unknown transfer classify failures.

module Data.Macaw.Refinement.UnknownTransfer
  ( symbolicUnkTransferRefinement
  )
where

import           Data.Macaw.Discovery.State

symbolicUnkTransferRefinement :: DiscoveryState arch -> DiscoveryState arch
symbolicUnkTransferRefinement = id
