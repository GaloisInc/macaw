{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.RISCV.RISCVReg where

import qualified Data.Macaw.Memory as MM
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

data RISCVReg rv tp where
  PC  :: RISCVReg rv (MT.BVType (G.RVWidth rv))
  GPR :: BV.BitVector 5 -> RISCVReg rv (MT.BVType (G.RVWidth rv))
  FPR :: BV.BitVector 5 -> RISCVReg rv (MT.BVType (G.RVFloatWidth rv))
  CSR :: G.CSR -> RISCVReg rv (MT.BVType (G.RVWidth rv))
  PrivLevel :: RISCVReg rv (MT.BVType 2)
  EXC :: RISCVReg rv MT.BoolType

ra :: RISCVReg rv (MT.BVType (G.RVWidth rv))
ra = GPR 0x01

instance Show (RISCVReg rv tp) where
  show PC = "pc"
  show (GPR 1) = "ra"
  show (GPR 2) = "sp"
  show (GPR 3) = "gp"
  show (GPR 4) = "tp"
  show (GPR 5) = "t0"
  show (GPR 6) = "t1"
  show (GPR 7) = "t2"
  show (GPR 8) = "s0"
  show (GPR 9) = "s1"
  show (GPR 10) = "a0"
  show (GPR 11) = "a1"
  show (GPR 12) = "a2"
  show (GPR 13) = "a3"
  show (GPR 14) = "a4"
  show (GPR 15) = "a5"
  show (GPR 16) = "a6"
  show (GPR 17) = "a7"
  show (GPR 18) = "s2"
  show (GPR 19) = "s3"
  show (GPR 20) = "s4"
  show (GPR 21) = "s5"
  show (GPR 22) = "s6"
  show (GPR 23) = "s7"
  show (GPR 24) = "s8"
  show (GPR 25) = "s9"
  show (GPR 26) = "s10"
  show (GPR 27) = "s11"
  show (GPR 28) = "t3"
  show (GPR 29) = "t4"
  show (GPR 30) = "t5"
  show (GPR 31) = "t6"
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

instance (G.KnownRV rv, RISCV rv) => MC.RegisterInfo (RISCVReg rv) where
  archRegs = riscvRegs
  archRegSet = riscvRegSet
  sp_reg = GPR 2
  ip_reg = PC
  syscall_num_reg = error "syscall_num_reg undefined"
  syscallArgumentRegs = error "syscallArgumentRegs undefined"

riscvAddrWidth :: G.RVRepr rv
               -> MM.AddrWidthRepr (MC.RegAddrWidth (MC.ArchReg rv))
riscvAddrWidth rvRepr = case G.rvBaseArch rvRepr of
  G.RV32Repr -> MM.Addr32
  G.RV64Repr -> MM.Addr64
  G.RV128Repr -> error "RV128 not supported"
