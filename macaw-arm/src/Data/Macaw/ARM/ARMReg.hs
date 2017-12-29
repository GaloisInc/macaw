-- | Defines the register types for ARM, along with some helpers

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.ARM.ARMReg
    ( ARMReg(..)
    )
    where

import           GHC.TypeLits
import qualified Data.Macaw.CFG as MC
import qualified SemMC.ARM as ARM
import           Data.Macaw.Types ( BVType )

data ARMReg tp where
    ARM_IP :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => ARMReg (BVType w)

deriving instance Eq (ARMReg tp)
deriving instance Ord (ARMReg tp)

instance Show (ARMReg tp) where
    show r = case r of
               ARM_IP -> "ip"

-- instance ShowF ARMReg where
--     showF = show

type instance MC.ArchReg ARM.ARM = ARMReg
type instance MC.RegAddrWidth ARMReg = 32
