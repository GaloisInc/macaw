module Data.Macaw.BinaryLoader.ELF (
  resolveAbsoluteAddress
  ) where

import           Data.Maybe ( listToMaybe )

import qualified Data.Macaw.Memory as MM

-- | Resolve a 'MM.MemWord', interpreted as an absolute address, into a 'MM.MemSegmentOff'
--
-- This is useful for resolving the entry point of a binary into a macaw
-- address.  At the level of an ELF file (or other executable container),
-- addresses are given as "absolute" addresses.  This is a bit of a convenient
-- fiction as the real address cannot be known until load time when the OS (or
-- bootleader) maps the executable into memory at some offset.  In some sense,
-- all of the addresses given in the executable container are *offsets from an abstract base*.
--
-- Macaw loads dynamically linked and statically linked binaries slightly
-- differently, where addresses in the statically linked case are all "absolute"
-- with region number 0.  Dynamically linked executables have a different region
-- number.  This function searches for the segment containing the ostensibly
-- absolute address and converts it into a 'MM.MemSegmentOff'.
resolveAbsoluteAddress
  :: (MM.MemWidth w)
  => MM.Memory w
  -> MM.MemWord w
  -> Maybe (MM.MemSegmentOff w)
resolveAbsoluteAddress mem addr =
  listToMaybe [ segOff
              | seg <- MM.memSegments mem
              , let region = MM.segmentBase seg
              , Just segOff <- return (MM.resolveRegionOff mem region addr)
              ]
