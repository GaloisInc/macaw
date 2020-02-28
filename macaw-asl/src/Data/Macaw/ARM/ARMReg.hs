-- | Defines the register types and names/locations for ARM, along
-- with some helpers

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.ARM.ARMReg
    ( ARMReg(..)
    -- , armRegToGPR
    , arm_LR
    -- , ArchWidth(..)
    , linuxSystemCallPreservedRegisters
    , locToRegTH
    )
    where

import           Data.Parameterized.Classes
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Parameterized.TH.GADT as TH
import qualified Data.Set as Set
import           Data.Word ( Word32 )
import           GHC.TypeLits
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax ( lift )
import qualified Text.PrettyPrint.HughesPJClass as PP

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types  as MT
-- ( TypeRepr(..), HasRepr, BVType
--                                   , typeRepr, n32 )
import qualified Dismantle.ARM.A32 as DA
import qualified Language.ASL.Globals as ASL
import qualified SemMC.Architecture.AArch32 as SA
import qualified SemMC.Architecture.ARM.Location as SA
import qualified What4.BaseTypes as WT

type family BaseToMacawType (tp :: WT.BaseType) :: MT.Type where
  BaseToMacawType (WT.BaseBVType w) = MT.BVType w
  BaseToMacawType WT.BaseBoolType = MT.BoolType

baseToMacawTypeRepr :: WT.BaseTypeRepr tp -> MT.TypeRepr (BaseToMacawType tp)
baseToMacawTypeRepr (WT.BaseBVRepr w) = MT.BVTypeRepr w
baseToMacawTypeRepr WT.BaseBoolRepr = MT.BoolTypeRepr
baseToMacawTypeRepr _ = error "ARMReg: unsupported what4 type"

-- | Defines the Register set for the ARM processor.
data ARMReg tp where
  -- | 'ASL.GlobalRef' that refers to a bitvector.
  ARMGlobalBV :: ( tp ~ BVType w
                 , 1 <= w
                 , tp' ~ ASL.GlobalsType s
                 , tp ~ BaseToMacawType tp')
              => ASL.GlobalRef s -> ARMReg tp
  -- | 'ASL.GlobalRef' that refers to a boolean.
  ARMGlobalBool :: ( tp ~ BoolType
                   , tp' ~ ASL.GlobalsType s
                   , tp ~ BaseToMacawType tp')
                => ASL.GlobalRef s -> ARMReg tp

numGPR :: Word32
numGPR = 16

-- -- | GPR14 is the link register for ARM
arm_LR :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => ARMReg (BVType w)
arm_LR = ARMGlobalBV (ASL.knownGlobalRef @"_R14")

-- armRegToGPR :: ARMReg tp -> Maybe DA.GPR
-- armRegToGPR (ARM_GP gp) = Just (ARMOperands.gpr gp)
-- armRegToGPR _ = Nothing

-- deriving instance Eq (ARMReg tp)
-- deriving instance Ord (ARMReg tp)

instance Show (ARMReg tp) where
  show r = case r of
    ARMGlobalBV globalRef -> show (ASL.globalRefSymbol globalRef)
    ARMGlobalBool globalRef -> show (ASL.globalRefSymbol globalRef)

instance ShowF ARMReg where
    showF = show

$(return [])  -- allow template haskell below to see definitions above

instance TestEquality ARMReg where
    testEquality = $(TH.structuralTypeEquality [t| ARMReg |]
                      [ (TH.ConType [t|ASL.GlobalRef|]
                         `TH.TypeApp` TH.AnyType,
                         [|testEquality|])
                      ])

instance EqF ARMReg where
  r1 `eqF` r2 = isJust (r1 `testEquality` r2)

instance Eq (ARMReg tp) where
  r1 == r2 = r1 `eqF` r2

instance OrdF ARMReg where
  compareF = $(TH.structuralTypeOrd [t| ARMReg |]
                [ (TH.ConType [t|ASL.GlobalRef|]
                    `TH.TypeApp` TH.AnyType,
                    [|compareF|])
                ])

instance Ord (ARMReg tp) where
  r1 `compare` r2 = toOrdering (r1 `compareF` r2)


instance HasRepr ARMReg TypeRepr where
    typeRepr r =
        case r of
          ARMGlobalBV globalRef -> baseToMacawTypeRepr (ASL.globalRefRepr globalRef)
          ARMGlobalBool globalRef -> baseToMacawTypeRepr (ASL.globalRefRepr globalRef)

type instance MC.ArchReg SA.AArch32 = ARMReg
type instance MC.RegAddrWidth ARMReg = 32

instance ( 1 <= MC.RegAddrWidth ARMReg
         , KnownNat (MC.RegAddrWidth ARMReg)
         , MM.MemWidth (MC.RegAddrWidth (MC.ArchReg SA.AArch32))
         , MC.ArchReg SA.AArch32 ~ ARMReg
         -- , ArchWidth arm
         ) =>
    MC.RegisterInfo ARMReg where
      archRegs = armRegs
      sp_reg = ARMGlobalBV (ASL.knownGlobalRef @"_R13")
--      sp_reg = ARM_GP 13
      ip_reg = ARMGlobalBV (ASL.knownGlobalRef @"_PC")
--      ip_reg = ARM_PC
      syscall_num_reg = error "TODO: MC.RegisterInfo ARMReg syscall_num_reg undefined"
      syscallArgumentRegs = error "TODO: MC.RegisterInfo ARMReg syscallArgumentsRegs undefined"

armRegs :: forall w. (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => [Some ARMReg]
armRegs = [ Some (ARMGlobalBV (ASL.knownGlobalRef @"_R1"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R2"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R3"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R4"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R5"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R6"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R7"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R8"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R9"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R10"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R11"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R12"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R13"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R14"))
          , Some (ARMGlobalBV (ASL.knownGlobalRef @"_PC"))
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
  Set.fromList [ Some (ARMGlobalBV (ASL.knownGlobalRef @"_R8"))
               , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R9"))
               , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R10"))
               , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R11"))
               , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R12"))
               , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R13"))
               , Some (ARMGlobalBV (ASL.knownGlobalRef @"_R14"))
               , Some (ARMGlobalBV (ASL.knownGlobalRef @"_PC"))
               ]
  -- Currently, we are only considering the non-volatile GPRs.  There
  -- are also a set of non-volatile floating point registers.  I have
  -- to check on the vector registers.


-- | Translate a location from the semmc semantics into a location suitable for
-- use in macaw
locToRegTH :: proxy arm
           -> SA.Location arm ctp
           -> Q Exp
locToRegTH _ (SA.Location globalRef) = case ASL.globalRefSymbol globalRef of
  _ -> [| error "locToRegTH undefined for unrecognized location" |]
-- locToRegTH _  Loc.LocPC      = [| ARM_PC |]
-- locToRegTH _  (Loc.LocGPR g) = [| ARM_GP ($(lift g)) |]
-- locToRegTH _  _              = [| error "locToRegTH undefined for unrecognized location" |]
