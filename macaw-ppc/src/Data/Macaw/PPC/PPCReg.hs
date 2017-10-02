{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

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

instance TestEquality PPCReg where
  testEquality x y = orderingIsEqual (compareF x y)
    where
      orderingIsEqual :: OrderingF (x :: k) (y :: k) -> Maybe (x :~: y)
      orderingIsEqual o =
        case o of
          LTF -> Nothing
          EQF -> Just Refl
          GTF -> Nothing

instance OrdF PPCReg where
  compareF (PPC_GP n) (PPC_GP n') = fromOrdering (compare n n')
  compareF PPC_GP{} _ = LTF
  compareF _ PPC_GP{} = GTF
