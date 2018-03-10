-- | Defines the register types and names/locations for ARM, along
-- with some helpers

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
    , arm_LR
    -- , ArchWidth(..)
    , linuxSystemCallPreservedRegisters
    , locToRegTH
    )
    where

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types ( TypeRepr(..), HasRepr, BVType
                                  , typeRepr, n32 )
import           Data.Parameterized.Classes
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TH.GADT as TH
import           Data.Semigroup
import qualified Data.Set as Set
import           Data.Word ( Word8 )
import           GHC.TypeLits
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax ( lift )
import qualified SemMC.ARM as ARM
import qualified SemMC.Architecture.ARM.Location as Loc
import qualified Text.PrettyPrint.HughesPJClass as PP


data ARMReg tp where
    -- n.b. The Thumb (T32) register model is the same as the ARM
    -- (A32) model, so just use the latter to define registers.
    ARM_GP :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => Word8 -> ARMReg (BVType w)
             -- GPR15 is normally aliased with the PC, but not always,
             -- so track it separately and use semantics definitions
             -- to manage the synchronization.
    ARM_PC :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => ARMReg (BVType w)
    ARM_CPSR :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => ARMReg (BVType w)

-- | GPR14 is the link register for ARM
arm_LR :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => ARMReg (BVType w)
arm_LR = ARM_GP 14


deriving instance Eq (ARMReg tp)
deriving instance Ord (ARMReg tp)

instance Show (ARMReg tp) where
    show r = case r of
               ARM_GP gpr_oper -> show $ PP.pPrint gpr_oper
                               --   case unGPRrnum of
                               -- 15 -> show rnum <> "=PC"
                               -- 14 -> show rnum <> "=LR"
                               -- 13 -> show rnum <> "=SP"
                               -- _ -> show rnum
               ARM_PC -> "<PC>"
               ARM_CPSR -> "<CPSR>"


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
          ARM_GP {} -> BVTypeRepr n32
          ARM_PC -> BVTypeRepr n32
          ARM_CPSR -> BVTypeRepr n32


type instance MC.ArchReg ARM.ARM = ARMReg
type instance MC.RegAddrWidth ARMReg = 32


instance ( 1 <= MC.RegAddrWidth ARMReg
         , KnownNat (MC.RegAddrWidth ARMReg)
         , MM.MemWidth (MC.RegAddrWidth (MC.ArchReg ARM.ARM))
         , MC.ArchReg ARM.ARM ~ ARMReg
         -- , ArchWidth arm
         ) =>
    MC.RegisterInfo ARMReg where
      archRegs = armRegs
      sp_reg = ARM_GP 13
      ip_reg = ARM_PC
      syscall_num_reg = error "MC.RegisterInfo ARMReg syscall_num_reg undefined"
      syscallArgumentRegs = error "MC.RegisterInfo ARMReg syscallArgumentsRegs undefined"

armRegs :: forall w. (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => [Some ARMReg]
armRegs = [ Some (ARM_GP n) | n <- [0..ARM.numGPR-1] ] <>
          [ Some ARM_PC
          , Some ARM_CPSR
          ]


-- | The set of registers preserved across Linux system calls is defined by the ABI.
--
-- According to
-- https://stackoverflow.com/questions/12946958/system-call-in-arm,
-- R0-R6 are used to pass syscall arguments, r7 specifies the
-- syscall#, and r0 is the return code.
linuxSystemCallPreservedRegisters :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w)
                                  => proxy arm
                                  -> Set.Set (Some ARMReg)
linuxSystemCallPreservedRegisters _ =
  Set.fromList [ Some (ARM_GP rnum) | rnum <- [8..ARM.numGPR-1] ]
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
locToRegTH _  Loc.LocPC      = [| ARM_PC |]
locToRegTH _  (Loc.LocGPR g) = [| ARM_GP ($(lift g)) |]
locToRegTH _  (Loc.LocCPSR)  = [| ARM_CPSR |]
locToRegTH _  _              = [| error "locToRegTH undefined for unrecognized location" |]
