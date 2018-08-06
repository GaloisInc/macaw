{-| Re-exports the modules responsible for representing views of memory as well
  as tools for generating those views from binaries.
-}
module Data.Macaw.Memory
  ( module Data.Macaw.Memory.Common
  , module Data.Macaw.Memory.Permissions
  , memoryForElf
  ) where

import Data.Macaw.Memory.Common
import Data.Macaw.Memory.ElfLoader ( memoryForElf )
import Data.Macaw.Memory.Permissions
