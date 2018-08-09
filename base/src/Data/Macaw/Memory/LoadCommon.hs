{-|
Copyright   : (c) Galois Inc, 2016
Maintainer  : jhendrix@galois.com

Common datatypes for creating a memory from a binary file.
-}
module Data.Macaw.Memory.LoadCommon
  ( LoadOptions(..)
  , defaultLoadOptions
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
   = LoadOptions { loadRegionIndex :: !(Maybe RegionIndex)
                   -- ^ Defines the /region/ to load sections and segments into.
                   --
                   -- This should be 0 for static libraries since their addresses are
                   -- absolute.  It should likely be non-zero for shared library since their
                   -- addresses are relative.  Different shared libraries loaded into the
                   -- same memory should have different region indices.
                   --
                   -- If 'Nothing' then static executables have region index 0 and other
                   -- files have region index 1.
                 , loadRegionBaseOffset :: !Integer
                   -- ^ Increment to automatically add to segment/section memory offsets
                   -- when loading.
                   --
                   -- This defaults to '0', and is primarily intended to allow loading
                   -- relocatable files at specific hard-coded offsets.
                 }

-- | Default options for loading
defaultLoadOptions :: LoadOptions
defaultLoadOptions =
  LoadOptions { loadRegionIndex = Nothing
              , loadRegionBaseOffset = 0
              }
