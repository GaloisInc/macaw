{-|
Copyright   : (c) Galois Inc, 2016
Maintainer  : jhendrix@galois.com

Common datatypes for creating a memory from a binary file.
-}
module Data.Macaw.Memory.LoadCommon
  ( LoadOptions(..)
  , LoadStyle(..)
  ) where

import Data.Macaw.Memory

------------------------------------------------------------------------
-- LoadOptions

-- | How to load Elf file.
data LoadStyle
   = LoadBySection
     -- ^ Load loadable sections in Elf file.
   | LoadBySegment
     -- ^ Load segments in Elf file.
  deriving (Eq)

-- | Options used to configure loading
data LoadOptions
   = LoadOptions { loadRegionIndex :: !RegionIndex
                   -- ^ Defines the "region" to load sections and segments into.
                   --
                   -- This should be 0 for static libraries since their addresses are
                   -- absolute.  It should likely be non-zero for shared library since their
                   -- addresses are relative.  Different shared libraries loaded into the
                   -- same memory should have different region indices.
                 , loadStyle :: !LoadStyle
                   -- ^ Controls whether to load by section or segment
                 , includeBSS :: !Bool
                   -- ^ Include data not backed by file when creating memory segments.
                 }
