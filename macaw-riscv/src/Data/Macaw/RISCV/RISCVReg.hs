{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.RISCV.RISCVReg where

import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.CFG as MC

import           Data.Parameterized.Classes
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.NatRepr (knownNat)
import           Data.Parameterized.TH.GADT ( structuralTypeEquality
                                            , structuralTypeOrd
                                            )
import           Data.Functor.Const

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Map as MapF
import qualified GRIFT.Types as GT

data RISCVReg rv tp where
  PC  :: RISCVReg rv (MT.BVType (GT.RVWidth rv))
  GPR :: BV.BitVector 5 -> RISCVReg rv (MT.BVType (GT.RVWidth rv))
  FPR :: BV.BitVector 5 -> RISCVReg rv (MT.BVType (GT.RVFloatWidth rv))
  CSR :: CSR -> RISCVReg rv (MT.BVType (GT.RVWidth rv))
  PrivLevel :: RISCVReg rv (MT.BVType 2)

data CSR = MCause

instance Eq CSR where
  (==) = undefined

instance Ord CSR where
  compare = undefined

instance Show CSR where
  show = undefined

instance Show (RISCVReg rv tp) where
  show PC = "pc"
  show (GPR rid) = "gpr[" <> show rid <> "]"
  show (FPR rid) = "fpr[" <> show rid <> "]"
  show (CSR csr) = show csr
  show (PrivLevel) = "priv"

$(return [])

instance TestEquality (RISCVReg rv) where
  testEquality = $(structuralTypeEquality [t|RISCVReg|] [])

instance OrdF (RISCVReg rv) where
  compareF = $(structuralTypeOrd [t|RISCVReg|] [])

instance ShowF (RISCVReg rv)

instance GT.KnownRV rv => MT.HasRepr (RISCVReg rv) MT.TypeRepr where
  typeRepr PC = MT.BVTypeRepr knownNat
  typeRepr (GPR _) = MT.BVTypeRepr knownNat
  typeRepr (FPR _) = MT.BVTypeRepr knownNat
  typeRepr (CSR _) = MT.BVTypeRepr knownNat
  typeRepr PrivLevel = MT.BVTypeRepr knownNat

type instance MC.ArchReg rv = RISCVReg rv
type instance MC.RegAddrWidth (RISCVReg rv) = GT.RVWidth rv

type RISCV rv = ( GT.KnownRV rv
                , MM.MemWidth (GT.RVWidth rv)
                )

riscvRegs :: [Some (RISCVReg rv)]
riscvRegs = [Some PC] ++
             ((Some . GPR) <$> [1..31]) ++
             ((Some . FPR) <$> [0..31]) ++
             [Some (CSR MCause)] ++
             [Some PrivLevel]

riscvRegSet :: MapF.MapF (RISCVReg rv) (Const ())
riscvRegSet = MapF.fromList (mkPair <$> riscvRegs)
  where mkPair (Some reg) = MapF.Pair reg (Const ())

instance RISCV rv => MC.RegisterInfo (RISCVReg rv) where
  archRegs = riscvRegs
  archRegSet = riscvRegSet
  sp_reg = GPR 2
  ip_reg = PC
  syscall_num_reg = error "syscall_num_reg undefined"
  syscallArgumentRegs = error "syscallArgumentRegs undefined"
