-- | Defines the register types for ARM, along with some helpers

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.ARM.ARMReg
    ( ARMReg(..)
    -- , ArchWidth(..)
    )
    where

import qualified Data.Macaw.CFG as MC
import           Data.Macaw.Types ( TypeRepr(..), HasRepr, BVType
                                  , typeRepr, n32 )
import           Data.Parameterized.Classes
import           Data.Parameterized.Some ( Some(..) )
import           GHC.TypeLits
import qualified Data.Parameterized.TH.GADT as TH
import qualified SemMC.ARM as ARM


data ARMReg tp where
    ARM_IP :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => ARMReg (BVType w)

deriving instance Eq (ARMReg tp)
deriving instance Ord (ARMReg tp)

instance Show (ARMReg tp) where
    show r = case r of
               ARM_IP -> "ip"

instance ShowF ARMReg where
    showF = show

$(return [])  -- allow template haskell below to see definitions above

instance TestEquality ARMReg where
    testEquality = $(TH.structuralTypeEquality [t| ARMReg |] [])

instance OrdF ARMReg where
    compareF = $(TH.structuralTypeOrd [t| ARMReg |] [])

instance HasRepr ARMReg TypeRepr where
    typeRepr r =
        case r of
          ARM_IP -> BVTypeRepr n32

type instance MC.ArchReg ARM.ARM = ARMReg
type instance MC.RegAddrWidth ARMReg = 32


instance ( 1 <= MC.RegAddrWidth ARMReg
         , KnownNat (MC.RegAddrWidth ARMReg)
         -- , MM.MemWidth (MC.RegAddrWidth (MC.ArchReg arm))
         -- , MC.ArchReg arm ~ ARMReg
         -- , ArchWidth arm
         ) =>
    MC.RegisterInfo ARMReg where
      archRegs = armRegs
      sp_reg = undefined
      ip_reg = ARM_IP
      syscall_num_reg = undefined
      syscallArgumentRegs = undefined

armRegs :: forall w. (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => [Some ARMReg]
armRegs = [ Some ARM_IP ]
