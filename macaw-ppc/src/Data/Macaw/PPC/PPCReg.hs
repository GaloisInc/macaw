{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Macaw.PPC.PPCReg (
  PPCReg(..)
  ) where

import           Data.Macaw.Types
import           Data.Parameterized.Classes
import qualified Data.Parameterized.TH.GADT as TH
import qualified Dismantle.PPC as D

data PPCReg tp where
  PPC_GP :: D.GPR -> PPCReg (BVType 64)

deriving instance Eq (PPCReg tp)
deriving instance Ord (PPCReg tp)

instance Show (PPCReg tp) where
  show (PPC_GP r) = show r

instance ShowF PPCReg where
  showF = show

$(return [])

instance TestEquality PPCReg where
  testEquality = $(TH.structuralTypeEquality [t| PPCReg |] [])

instance OrdF PPCReg where
  compareF = $(TH.structuralTypeOrd [t| PPCReg |] [])
