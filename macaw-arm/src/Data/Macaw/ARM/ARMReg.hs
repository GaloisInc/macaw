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
    , linuxSystemCallPreservedRegisters
    , locToRegTH
    )
    where

import qualified Data.Macaw.CFG as MC
import           Data.Macaw.Types ( TypeRepr(..), HasRepr, BVType
                                  , typeRepr, n32 )
import           Data.Parameterized.Classes
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TH.GADT as TH
import qualified Data.Set as Set
import           GHC.TypeLits
import           Language.Haskell.TH
import qualified SemMC.ARM as ARM
import qualified SemMC.Architecture.ARM.Location as Loc


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


-- | The set of registers preserved across Linux system calls is defined by the ABI.
--
-- NOTE: As the name implies, this is Linux-specific.  Other ABIs will require
-- an analysis here.  That said, these are the register specs suggested by the
-- architecture manual, so they should be pretty consistent across ABIs.
linuxSystemCallPreservedRegisters :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w)
                                  => proxy arm
                                  -> Set.Set (Some ARMReg)
linuxSystemCallPreservedRegisters _ =
  Set.fromList [] -- Some (PPC_GP (D.GPR rnum)) | rnum <- [14..31] ]
  -- Currently, we are only considering the non-volatile GPRs.  There
  -- are also a set of non-volatile floating point registers.  I have
  -- to check on the vector registers.


-- | Translate a location from the semmc semantics into a location suitable for
-- use in macaw
locToRegTH :: (1 <= Loc.ArchRegWidth arm,
               MC.RegAddrWidth ARMReg ~ Loc.ArchRegWidth arm)
           => proxy arm
           -> Loc.Location arm ctp
           -> Q Exp
-- locToRegTH _ (Loc.LocGPR (D.GPR gpr)) = [| PPC_GP (D.GPR $(lift gpr)) |]
locToRegTH _  Loc.LocIP       = [| ARM_IP |]
locToRegTH _  _                = [| undefined |]
