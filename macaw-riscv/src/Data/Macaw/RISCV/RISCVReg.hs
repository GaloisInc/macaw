{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.RISCV.RISCVReg
  ( -- * RISC-V macaw register state
    RISCVReg(..)
    -- ** Patterns for GPRs
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
import           Data.Functor.Const

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Map as MapF
import qualified GRIFT.Types as G
import qualified GRIFT.Semantics.Utils as G

-- | RISC-V register.
data RISCVReg rv tp where
  -- | Program counter.
  PC  :: RISCVReg rv (MT.BVType (G.RVWidth rv))
  -- | General-purpose registers. GPR[0] is not really a register, so
  -- it should never be directly read from or written to.
  GPR :: BV.BitVector 5 -> RISCVReg rv (MT.BVType (G.RVWidth rv))
  -- | Floating-point registers.
  FPR :: BV.BitVector 5 -> RISCVReg rv (MT.BVType (G.RVFloatWidth rv))
  -- | Control/status registers.
  CSR :: G.CSR -> RISCVReg rv (MT.BVType (G.RVWidth rv))
  -- | Current privilege level.
  PrivLevel :: RISCVReg rv (MT.BVType 2)
  -- | Trip this if something bad happens.
  EXC :: RISCVReg rv MT.BoolType

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
  show GPR_RA = "ra"
  show GPR_SP = "sp"
  show GPR_GP = "gp"
  show GPR_TP = "tp"
  show GPR_T0 = "t0"
  show GPR_T1 = "t1"
  show GPR_T2 = "t2"
  show GPR_S0 = "s0"
  show GPR_S1 = "s1"
  show GPR_A0 = "a0"
  show GPR_A1 = "a1"
  show GPR_A2 = "a2"
  show GPR_A3 = "a3"
  show GPR_A4 = "a4"
  show GPR_A5 = "a5"
  show GPR_A6 = "a6"
  show GPR_A7 = "a7"
  show GPR_S2 = "s2"
  show GPR_S3 = "s3"
  show GPR_S4 = "s4"
  show GPR_S5 = "s5"
  show GPR_S6 = "s6"
  show GPR_S7 = "s7"
  show GPR_S8 = "s8"
  show GPR_S9 = "s9"
  show GPR_S10 = "s10"
  show GPR_S11 = "s11"
  show GPR_T3 = "t3"
  show GPR_T4 = "t4"
  show GPR_T5 = "t5"
  show GPR_T6 = "t6"
  show (GPR rid) = error $ "PANIC: bad gpr id " <> show rid
  show (FPR rid) = "fpr[" <> show rid <> "]"
  show (CSR csr) = show csr
  show PrivLevel = "priv"
  show EXC = "exc"

$(return [])

instance TestEquality (RISCVReg rv) where
  testEquality = $(structuralTypeEquality [t|RISCVReg|] [])

instance OrdF (RISCVReg rv) where
  compareF = $(structuralTypeOrd [t|RISCVReg|] [])

instance ShowF (RISCVReg rv)

instance G.KnownRV rv => MT.HasRepr (RISCVReg rv) MT.TypeRepr where
  typeRepr PC = MT.BVTypeRepr knownNat
  typeRepr (GPR _) = MT.BVTypeRepr knownNat
  typeRepr (FPR _) = MT.BVTypeRepr knownNat
  typeRepr (CSR _) = MT.BVTypeRepr knownNat
  typeRepr PrivLevel = MT.BVTypeRepr knownNat
  typeRepr EXC = MT.BoolTypeRepr

type instance MC.ArchReg rv = RISCVReg rv
type instance MC.RegAddrWidth (RISCVReg rv) = G.RVWidth rv

riscvRegs :: [Some (RISCVReg rv)]
riscvRegs = [Some PC] ++
             ((Some . GPR) <$> [1..31]) ++
             ((Some . FPR) <$> [0..31]) ++
             -- [Some (CSR MCause)] ++
             [Some PrivLevel, Some EXC]

riscvRegSet :: MapF.MapF (RISCVReg rv) (Const ())
riscvRegSet = MapF.fromList (mkPair <$> riscvRegs)
  where mkPair (Some reg) = MapF.Pair reg (Const ())

instance (G.KnownRV rv, RISCVConstraints rv) => MC.RegisterInfo (RISCVReg rv) where
  archRegs = riscvRegs
  archRegSet = riscvRegSet
  sp_reg = GPR_SP
  ip_reg = PC
  syscall_num_reg = error "syscall_num_reg undefined"
  syscallArgumentRegs = error "syscallArgumentRegs undefined"
