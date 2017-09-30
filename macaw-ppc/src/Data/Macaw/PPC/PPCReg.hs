{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Data.Macaw.PPC.PPCReg where

import Data.Macaw.Types
import Data.Parameterized.Classes
import Data.Parameterized.Some
import qualified Dismantle.PPC as D

data PPCReg tp where
  PPC_GP :: D.GPR -> PPCReg (BVType 64)

instance Show (PPCReg tp) where
  show (PPC_GP r) = show r

instance ShowF PPCReg where
  showF = show
