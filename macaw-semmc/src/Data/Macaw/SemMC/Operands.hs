{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
module Data.Macaw.SemMC.Operands (
  ExtractValue(..),
  ToRegister(..)
  ) where

import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.SemMC.Generator as G

class ExtractValue arch a tp | arch a -> tp where
  extractValue :: a -> G.Generator arch ids s (MC.Value arch ids tp)

class ToRegister a r tp | a r -> tp where
  toRegister :: a -> r tp
