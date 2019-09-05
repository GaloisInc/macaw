{-|
Copyright   : (c) Galois Inc, 2016
Maintainer  : jhendrix@galois.com

Common datatypes for creating a memory from a binary file.
-}
module Data.Macaw.Memory.LoadCommon
  ( LoadOptions(..)
  , loadRegionIndex
  , loadRegionBaseOffset
  , defaultLoadOptions
  , LoadStyle(..)
  ) where

import Data.Macaw.Memory
import Data.Word

------------------------------------------------------------------------
-- LoadOptions

-- | How to load Elf file.
data LoadStyle
   = LoadBySection
     -- ^ Load loadable sections in Elf file.
   | LoadBySegment
     -- ^ Load segments in Elf file.
  deriving (Eq)

-- | This contains options for loading.
newtype LoadOptions =
  LoadOptions { loadOffset :: Maybe Word64
                -- ^ If set, the Elf file should be loaded at a specific offset.
              }

loadRegionIndex :: LoadOptions -> Maybe RegionIndex
loadRegionIndex opts =
  case loadOffset opts of
    Nothing -> Nothing
    Just _ -> Just 0

loadRegionBaseOffset :: LoadOptions -> Integer
loadRegionBaseOffset opts =
  case loadOffset opts of
    Nothing -> 0
    Just o -> toInteger o

defaultLoadOptions :: LoadOptions
defaultLoadOptions = LoadOptions { loadOffset = Nothing }
