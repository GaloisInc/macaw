{-# LANGUAGE TypeFamilies #-}

module Data.Macaw.PPC.ArchTypes
  ( PPC64.PPC
  ) where

import Data.Macaw.CFG
import Data.Macaw.Types

import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64

import Data.Macaw.PPC.PPCReg


------------------------------------------------------------------------
-- PPC specific declarations

