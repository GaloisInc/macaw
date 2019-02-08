-- | This module uses symbolic evaluation to refine the discovered CFG
-- and determine possible targets for transfers.

module Data.Macaw.Refinement.Target
  ( symbolicTargetRefinement
  )
where

import           Data.Macaw.Discovery.State

symbolicTargetRefinement :: DiscoveryState arch -> DiscoveryState arch
symbolicTargetRefinement = id
