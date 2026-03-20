-- | This module provides a drop-in replacement for
-- "Data.Macaw.Symbolic.Memory". Unlike the memory model configuration in that
-- model, which populates the entire static memory in an SMT array before
-- beginning simulation, the memory model in this module lazily populates the
-- SMT array. That is, it will begin simulation without populating the SMT array
-- at all, and it instead checks before each read and write to see if a certain
-- part of the SMT array needs to be populated. This memory model also makes an
-- effort to avoid reading from the SMT array if performing concrete reads from
-- read-only sections of memory. The net result is that the lazy memory
-- sacrifices some extra space in exchange for generally improved simulation
-- times. For the full details on how this works, see
-- @Note [Lazy memory model]@.
--
-- Because the API in this module clashes with the API in
-- "Data.Macaw.Symbolic.Memory", it is recommended that you import these modules
-- with qualified imports.
module Data.Macaw.Symbolic.Memory.Lazy (
  -- * Memory Management
  memModelConfig,
  MemPtrTable,
  MSMC.toCrucibleEndian,
  MSMC.fromCrucibleEndian,
  MSMC.GlobalMemoryHooks(..),
  MSMC.defaultGlobalMemoryHooks,
  newGlobalMemory,
  newGlobalMemoryWith,
  newMergedGlobalMemoryWith,
  MSMC.MemoryModelContents(..),
  MSMC.MacawProcessAssertion,
  MSMC.MacawError(..),
  MSMC.defaultProcessMacawAssertion,
  mkGlobalPointerValidityPred,
  mapRegionPointers
  ) where

import qualified Data.Macaw.Symbolic.Memory.Common as MSMC
import Data.Macaw.Symbolic.Memory.Lazy.Internal
  ( MemPtrTable
  , memModelConfig
  , newGlobalMemory
  , newGlobalMemoryWith
  , newMergedGlobalMemoryWith
  , mkGlobalPointerValidityPred
  , mapRegionPointers
  )
