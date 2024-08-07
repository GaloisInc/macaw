{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Macaw.RISCV.RISCVReg
  ( -- * RISC-V macaw register state
    RISCVReg(..)
  , GPR(..)
    -- ** Patterns for GPRs
  , pattern GPR
  , pattern GPR_RA
  , pattern GPR_SP
  , pattern GPR_GP
  , pattern GPR_TP
  , pattern GPR_T0
  , pattern GPR_T1
  , pattern GPR_T2
  , pattern GPR_S0
  , pattern GPR_S1
  , pattern GPR_A0
  , pattern GPR_A1
  , pattern GPR_A2
  , pattern GPR_A3
  , pattern GPR_A4
  , pattern GPR_A5
  , pattern GPR_A6
  , pattern GPR_A7
  , pattern GPR_S2
  , pattern GPR_S3
  , pattern GPR_S4
  , pattern GPR_S5
  , pattern GPR_S6
  , pattern GPR_S7
  , pattern GPR_S8
  , pattern GPR_S9
  , pattern GPR_S10
  , pattern GPR_S11
  , pattern GPR_T3
  , pattern GPR_T4
  , pattern GPR_T5
  , pattern GPR_T6
  ) where

import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.CFG as MC

import           Data.Macaw.RISCV.Arch

import           Data.Parameterized.Classes
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.NatRepr (knownNat)
import           Data.Parameterized.TH.GADT ( structuralTypeEquality
                                            , structuralTypeOrd
                                            )

import qualified Prettyprinter as PP

import qualified GRIFT.Types as G
import qualified GRIFT.Semantics.Utils as G

newtype GPR = BuildGPR (G.SizedBV 5)
  deriving (Enum, Eq, Ord)

-- | Return address
pattern RA :: GPR
pattern RA = BuildGPR 1

-- | Stack pointer
pattern SP :: GPR
pattern SP = BuildGPR 2

-- | Global pointer
pattern GP :: GPR
pattern GP = BuildGPR 3

-- | Thread pointer
pattern TP :: GPR
pattern TP = BuildGPR 4

-- | Temporary/Alternate link register
pattern T0 :: GPR
pattern T0 = BuildGPR 5

-- | Temporary
pattern T1 :: GPR
pattern T1 = BuildGPR 6

-- | Temporary
pattern T2 :: GPR
pattern T2 = BuildGPR 7

-- | Saved register/frame pointer
pattern S0 :: GPR
pattern S0 = BuildGPR 8

-- | Saved register
pattern S1 :: GPR
pattern S1 = BuildGPR 9

-- | Function argument/return value
pattern A0 :: GPR
pattern A0 = BuildGPR 10

-- | Function argument/return value
pattern A1 :: GPR
pattern A1 = BuildGPR 11

-- | Function argument
pattern A2 :: GPR
pattern A2 = BuildGPR 12

-- | Function argument
pattern A3 :: GPR
pattern A3 = BuildGPR 13

-- | Function argument
pattern A4 :: GPR
pattern A4 = BuildGPR 14

-- | Function argument
pattern A5 :: GPR
pattern A5 = BuildGPR 15

-- | Function argument
pattern A6 :: GPR
pattern A6 = BuildGPR 16

-- | Function argument
pattern A7 :: GPR
pattern A7 = BuildGPR 17

-- | Saved register
pattern S2 :: GPR
pattern S2 = BuildGPR 18

-- | Saved register
pattern S3 :: GPR
pattern S3 = BuildGPR 19

-- | Saved register
pattern S4 :: GPR
pattern S4 = BuildGPR 20

-- | Saved register
pattern S5 :: GPR
pattern S5 = BuildGPR 21

-- | Saved register
pattern S6 :: GPR
pattern S6 = BuildGPR 22

-- | Saved register
pattern S7 :: GPR
pattern S7 = BuildGPR 23

-- | Saved register
pattern S8 :: GPR
pattern S8 = BuildGPR 24

-- | Saved register
pattern S9 :: GPR
pattern S9 = BuildGPR 25

-- | Saved register
pattern S10 :: GPR
pattern S10 = BuildGPR 26

-- | Saved register
pattern S11 :: GPR
pattern S11 = BuildGPR 27

-- | Temporary
pattern T3 :: GPR
pattern T3 = BuildGPR 28

-- | Temporary
pattern T4 :: GPR
pattern T4 = BuildGPR 29

-- | Temporary
pattern T5 :: GPR
pattern T5 = BuildGPR 30

-- | Temporary
pattern T6 :: GPR
pattern T6 = BuildGPR 31

{-# COMPLETE
  RA, SP, GP, TP,
  A0, A1, A2, A3, A4, A5, A6, A7,
  S0, S1, S2, S3, S4, S5, S6, S7,
  S8, S9, S10, S11,
  T0, T1, T2, T3, T4, T5, T6 #-}

instance Show GPR where
  show RA = "ra"
  show SP = "sp"
  show GP = "gp"
  show TP = "tp"
  show T0 = "t0"
  show T1 = "t1"
  show T2 = "t2"
  show S0 = "s0"
  show S1 = "s1"
  show A0 = "a0"
  show A1 = "a1"
  show A2 = "a2"
  show A3 = "a3"
  show A4 = "a4"
  show A5 = "a5"
  show A6 = "a6"
  show A7 = "a7"
  show S2 = "s2"
  show S3 = "s3"
  show S4 = "s4"
  show S5 = "s5"
  show S6 = "s6"
  show S7 = "s7"
  show S8 = "s8"
  show S9 = "s9"
  show S10 = "s10"
  show S11 = "s11"
  show T3 = "t3"
  show T4 = "t4"
  show T5 = "t5"
  show T6 = "t6"

-- | RISC-V register.
data RISCVReg rv tp where
  -- | Program counter.
  PC  :: RISCVReg rv (MT.BVType (G.RVWidth rv))
  -- | General-purpose registers. GPR[0] is not really a register, so
  -- it should never be directly read from or written to.
  RISCV_GPR :: GPR -> RISCVReg rv (MT.BVType (G.RVWidth rv))
  -- | Floating-point registers.
  FPR :: G.SizedBV 5 -> RISCVReg rv (MT.BVType (G.RVFloatWidth rv))
  -- | Control/status registers.
  CSR :: G.CSR -> RISCVReg rv (MT.BVType (G.RVWidth rv))
  -- | Current privilege level.
  PrivLevel :: RISCVReg rv (MT.BVType 2)
  -- | Trip this if something bad happens.
  EXC :: RISCVReg rv MT.BoolType

pattern GPR ::
  forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
    G.SizedBV 5 -> RISCVReg rv tp
pattern GPR bv = RISCV_GPR (BuildGPR bv)

-- | Return address
pattern GPR_RA :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_RA = GPR 1

-- | Stack pointer
pattern GPR_SP :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_SP = GPR 2

-- | Global pointer
pattern GPR_GP :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_GP = GPR 3

-- | Thread pointer
pattern GPR_TP :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_TP = GPR 4

-- | Temporary/Alternate link register
pattern GPR_T0 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_T0 = GPR 5

-- | Temporary
pattern GPR_T1 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_T1 = GPR 6

-- | Temporary
pattern GPR_T2 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_T2 = GPR 7

-- | Saved register/frame pointer
pattern GPR_S0 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S0 = GPR 8

-- | Saved register
pattern GPR_S1 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S1 = GPR 9

-- | Function argument/return value
pattern GPR_A0 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_A0 = GPR 10

-- | Function argument/return value
pattern GPR_A1 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_A1 = GPR 11

-- | Function argument
pattern GPR_A2 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_A2 = GPR 12

-- | Function argument
pattern GPR_A3 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_A3 = GPR 13

-- | Function argument
pattern GPR_A4 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_A4 = GPR 14

-- | Function argument
pattern GPR_A5 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_A5 = GPR 15

-- | Function argument
pattern GPR_A6 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_A6 = GPR 16

-- | Function argument
pattern GPR_A7 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_A7 = GPR 17

-- | Saved register
pattern GPR_S2 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S2 = GPR 18

-- | Saved register
pattern GPR_S3 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S3 = GPR 19

-- | Saved register
pattern GPR_S4 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S4 = GPR 20

-- | Saved register
pattern GPR_S5 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S5 = GPR 21

-- | Saved register
pattern GPR_S6 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S6 = GPR 22

-- | Saved register
pattern GPR_S7 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S7 = GPR 23

-- | Saved register
pattern GPR_S8 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S8 = GPR 24

-- | Saved register
pattern GPR_S9 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_S9 = GPR 25

-- | Saved register
pattern GPR_S10 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                   RISCVReg rv tp
pattern GPR_S10 = GPR 26

-- | Saved register
pattern GPR_S11 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                   RISCVReg rv tp
pattern GPR_S11 = GPR 27

-- | Temporary
pattern GPR_T3 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_T3 = GPR 28

-- | Temporary
pattern GPR_T4 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_T4 = GPR 29

-- | Temporary
pattern GPR_T5 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_T5 = GPR 30

-- | Temporary
pattern GPR_T6 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVWidth rv)) =>
                  RISCVReg rv tp
pattern GPR_T6 = GPR 31

instance Show (RISCVReg rv tp) where
  show PC = "pc"
  show (RISCV_GPR gpr) = show gpr
  show (FPR rid) = "f" <> show (G.asUnsignedSized rid)
  show (CSR csr) = show csr
  show PrivLevel = "priv"
  show EXC = "exc"

$(return [])

instance TestEquality (RISCVReg rv) where
  testEquality = $(structuralTypeEquality [t|RISCVReg|] [])

instance OrdF (RISCVReg rv) where
  compareF = $(structuralTypeOrd [t|RISCVReg|] [])

instance ShowF (RISCVReg rv)

instance MC.PrettyF (RISCVReg rv) where
  prettyF = PP.pretty . showF

instance G.KnownRV rv => MT.HasRepr (RISCVReg rv) MT.TypeRepr where
  typeRepr PC = MT.BVTypeRepr knownNat
  typeRepr (RISCV_GPR _) = MT.BVTypeRepr knownNat
  typeRepr (FPR _) = MT.BVTypeRepr knownNat
  typeRepr (CSR _) = MT.BVTypeRepr knownNat
  typeRepr PrivLevel = MT.BVTypeRepr knownNat
  typeRepr EXC = MT.BoolTypeRepr

type instance MC.ArchReg (RISCV rv) = RISCVReg rv
type instance MC.RegAddrWidth (RISCVReg rv) = G.RVWidth rv

riscvRegs :: [Some (RISCVReg rv)]
riscvRegs = [Some PC] ++
             ((Some . GPR) <$> [1..31]) ++
             ((Some . FPR) <$> [0..31]) ++
             [Some PrivLevel, Some EXC]

instance (G.KnownRV rv, RISCVConstraints rv) => MC.RegisterInfo (RISCVReg rv) where
  archRegs = riscvRegs
  sp_reg = GPR_SP
  ip_reg = PC
  syscall_num_reg = error "syscall_num_reg undefined"
  syscallArgumentRegs = error "syscallArgumentRegs undefined"
