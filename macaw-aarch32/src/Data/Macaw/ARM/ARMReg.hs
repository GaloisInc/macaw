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
    , arm_LR
    , branchTaken
    , linuxSystemCallPreservedRegisters
    , locToRegTH
    , integerToReg
    , integerToSIMDReg
    , branchTakenReg
    )
    where

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.SymbolRepr as PSR
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.TH.GADT as PTH
import qualified Data.Set as Set
import qualified Data.Text as T
import           GHC.TypeLits
import qualified Language.Haskell.TH as TH
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types  as MT
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
--
-- Note that the unusual statements of the GADT types in the BV and Bool cases
-- are that way to make it easier to bring type variables into scope and allow
-- us to recover some extra type equalities when pattern matching.
data ARMReg tp where
  -- | 'ASL.GlobalRef' that refers to a bitvector.
  ARMGlobalBV :: ( tp ~ MT.BVType w
                 , 1 <= w
                 , tp' ~ ASL.GlobalsType s
                 , tp ~ BaseToMacawType tp')
              => ASL.GlobalRef s -> ARMReg tp
  -- | 'ASL.GlobalRef' that refers to a boolean.
  ARMGlobalBool :: ( tp ~ MT.BoolType
                   , tp' ~ ASL.GlobalsType s
                   , tp ~ BaseToMacawType tp')
                => ASL.GlobalRef s -> ARMReg tp
  ARMWriteMode :: tp ~ MT.BVType 2 => ARMReg (MT.BVType 2)

-- | GPR14 is the link register for ARM
arm_LR :: (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => ARMReg (MT.BVType w)
arm_LR = ARMGlobalBV (ASL.knownGlobalRef @"_R14")

branchTaken :: ARMReg MT.BoolType
branchTaken = ARMGlobalBool (ASL.knownGlobalRef @"__BranchTaken")

instance Show (ARMReg tp) where
  show r = case r of
    ARMGlobalBV globalRef -> show (ASL.globalRefSymbol globalRef)
    ARMGlobalBool globalRef -> show (ASL.globalRefSymbol globalRef)
    ARMWriteMode -> "ARMWriteMode"

instance ShowF ARMReg where
    showF = show

instance MC.PrettyF ARMReg where
  prettyF = PP.text . showF

$(return [])  -- allow template haskell below to see definitions above

instance TestEquality ARMReg where
    testEquality = $(PTH.structuralTypeEquality [t| ARMReg |]
                      [ (PTH.ConType [t|ASL.GlobalRef|]
                         `PTH.TypeApp` PTH.AnyType,
                         [|testEquality|])
                      ])

instance EqF ARMReg where
  r1 `eqF` r2 = isJust (r1 `testEquality` r2)

instance Eq (ARMReg tp) where
  r1 == r2 = r1 `eqF` r2

instance OrdF ARMReg where
  compareF = $(PTH.structuralTypeOrd [t| ARMReg |]
                [ (PTH.ConType [t|ASL.GlobalRef|]
                    `PTH.TypeApp` PTH.AnyType,
                    [|compareF|])
                ])

instance Ord (ARMReg tp) where
  r1 `compare` r2 = toOrdering (r1 `compareF` r2)


instance MT.HasRepr ARMReg MT.TypeRepr where
    typeRepr r =
        case r of
          ARMGlobalBV globalRef -> baseToMacawTypeRepr (ASL.globalRefRepr globalRef)
          ARMGlobalBool globalRef -> baseToMacawTypeRepr (ASL.globalRefRepr globalRef)
          ARMWriteMode -> MT.BVTypeRepr (NR.knownNat @2)

type instance MC.ArchReg SA.AArch32 = ARMReg
type instance MC.RegAddrWidth ARMReg = 32

instance ( 1 <= MC.RegAddrWidth ARMReg
         , KnownNat (MC.RegAddrWidth ARMReg)
         , MM.MemWidth (MC.RegAddrWidth (MC.ArchReg SA.AArch32))
         , MC.ArchReg SA.AArch32 ~ ARMReg
         ) =>
    MC.RegisterInfo ARMReg where
      archRegs = armRegs
      sp_reg = ARMGlobalBV (ASL.knownGlobalRef @"_R13")
      ip_reg = ARMGlobalBV (ASL.knownGlobalRef @"_PC")
      syscall_num_reg = error "TODO: MC.RegisterInfo ARMReg syscall_num_reg undefined"
      syscallArgumentRegs = error "TODO: MC.RegisterInfo ARMReg syscallArgumentsRegs undefined"

armRegs :: forall w. (w ~ MC.RegAddrWidth ARMReg, 1 <= w) => [Some ARMReg]
armRegs = FC.toListFC asARMReg ( FC.fmapFC ASL.SimpleGlobalRef ASL.simpleGlobalRefs Ctx.<++>
                                 ASL.gprGlobalRefsSym Ctx.<++>
                                 ASL.simdGlobalRefsSym
                               )
  where asARMReg :: ASL.GlobalRef s -> Some ARMReg
        asARMReg gr = case ASL.globalRefRepr gr of
          WT.BaseBoolRepr -> Some (ARMGlobalBool gr)
          WT.BaseBVRepr _ -> Some (ARMGlobalBV gr)
          tp -> error $ "unsupported global type " <> show tp

-- | The set of registers preserved across Linux system calls is defined by the ABI.
--
-- According to
-- https://stackoverflow.com/questions/12946958/system-call-in-arm,
-- R0-R6 are used to pass syscall arguments, r7 specifies the
-- syscall#, and r0 is the return code.
linuxSystemCallPreservedRegisters :: Set.Set (Some ARMReg)
linuxSystemCallPreservedRegisters =
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
locToRegTH :: SA.Location SA.AArch32 ctp
           -> TH.Q TH.Exp
locToRegTH (SA.Location globalRef) = do
  let refName = T.unpack (PSR.symbolRepr (ASL.globalRefSymbol globalRef))
  case ASL.globalRefRepr globalRef of
    WT.BaseBoolRepr ->
      [| ARMGlobalBool (ASL.knownGlobalRef :: ASL.GlobalRef $(return (TH.LitT (TH.StrTyLit refName)))) |]
    WT.BaseBVRepr _ ->
      [| ARMGlobalBV (ASL.knownGlobalRef :: ASL.GlobalRef $(return (TH.LitT (TH.StrTyLit refName)))) |]
    _tp -> [| error $ "locToRegTH undefined for unrecognized location: " <> $(return $ TH.LitE (TH.StringL refName)) |]

branchTakenReg :: ARMReg MT.BoolType
branchTakenReg = ARMGlobalBool (ASL.knownGlobalRef @"__BranchTaken")

integerToReg :: Integer -> Maybe (ARMReg (MT.BVType 32))
integerToReg 0  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R0")
integerToReg 1  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R1")
integerToReg 2  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R2")
integerToReg 3  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R3")
integerToReg 4  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R4")
integerToReg 5  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R5")
integerToReg 6  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R6")
integerToReg 7  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R7")
integerToReg 8  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R8")
integerToReg 9  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R9")
integerToReg 10 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R10")
integerToReg 11 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R11")
integerToReg 12 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R12")
integerToReg 13 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R13")
integerToReg 14 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_R14")
integerToReg _  = Nothing

integerToSIMDReg :: Integer -> Maybe (ARMReg (MT.BVType 128))
integerToSIMDReg 0  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V0")
integerToSIMDReg 1  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V1")
integerToSIMDReg 2  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V2")
integerToSIMDReg 3  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V3")
integerToSIMDReg 4  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V4")
integerToSIMDReg 5  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V5")
integerToSIMDReg 6  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V6")
integerToSIMDReg 7  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V7")
integerToSIMDReg 8  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V8")
integerToSIMDReg 9  = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V9")
integerToSIMDReg 10 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V10")
integerToSIMDReg 11 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V11")
integerToSIMDReg 12 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V12")
integerToSIMDReg 13 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V13")
integerToSIMDReg 14 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V14")
integerToSIMDReg 15 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V15")
integerToSIMDReg 16 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V16")
integerToSIMDReg 17 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V17")
integerToSIMDReg 18 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V18")
integerToSIMDReg 19 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V19")
integerToSIMDReg 20 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V20")
integerToSIMDReg 21 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V21")
integerToSIMDReg 22 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V22")
integerToSIMDReg 23 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V23")
integerToSIMDReg 24 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V24")
integerToSIMDReg 25 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V25")
integerToSIMDReg 26 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V26")
integerToSIMDReg 27 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V27")
integerToSIMDReg 28 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V28")
integerToSIMDReg 29 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V29")
integerToSIMDReg 30 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V30")
integerToSIMDReg 31 = Just $ ARMGlobalBV (ASL.knownGlobalRef @"_V31")
integerToSIMDReg _  = Nothing
