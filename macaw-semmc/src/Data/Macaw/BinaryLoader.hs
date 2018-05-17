{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Macaw.BinaryLoader (
  BinaryLoader(..),
  LoadedBinary(..)
  ) where

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.LoadCommon as LC

data LoadedBinary arch binImg =
  LoadedBinary { memoryImage :: MC.Memory (MC.ArchAddrWidth arch)
               , archBinaryData :: ArchBinaryData arch
               , binaryFormatData :: BinaryFormatData binImg
               , loadDiagnostics :: [Diagnostic binImg]
               }

class BinaryLoader arch binImg where
  type ArchBinaryData arch :: *
  type BinaryFormatData binImg :: *
  type Diagnostic binImg :: *
  loadBinary :: LC.LoadOptions -> binImg -> IO (LoadedBinary arch binImg)
