{-# LANGUAGE TypeFamilies #-}

module Data.Macaw.PPC.ArchTypes
  ( PPC
  ) where

import Data.Macaw.CFG
import Data.Macaw.Types

import Data.Macaw.PPC.PPCReg

------------------------------------------------------------------------
-- PPC specific declarations

data PPC

type instance ArchReg PPC = PPCReg
