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
  , FPR(..)
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
    -- ** Patterns for FPRs
  , pattern FPR
  , pattern FPR_FT0
  , pattern FPR_FT1
  , pattern FPR_FT2
  , pattern FPR_FT3
  , pattern FPR_FT4
  , pattern FPR_FT5
  , pattern FPR_FT6
  , pattern FPR_FT7
  , pattern FPR_FS0
  , pattern FPR_FS1
  , pattern FPR_FA0
  , pattern FPR_FA1
  , pattern FPR_FA2
  , pattern FPR_FA3
  , pattern FPR_FA4
  , pattern FPR_FA5
  , pattern FPR_FA6
  , pattern FPR_FA7
  , pattern FPR_FS2
  , pattern FPR_FS3
  , pattern FPR_FS4
  , pattern FPR_FS5
  , pattern FPR_FS6
  , pattern FPR_FS7
  , pattern FPR_FS8
  , pattern FPR_FS9
  , pattern FPR_FS10
  , pattern FPR_FS11
  , pattern FPR_FT8
  , pattern FPR_FT9
  , pattern FPR_FT10
  , pattern FPR_FT11
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

newtype FPR = BuildFPR (G.SizedBV 5)
  deriving (Enum, Eq, Ord)

-- | Temporary register
pattern FT0 :: FPR
pattern FT0 = BuildFPR 0

-- | Temporary register
pattern FT1 :: FPR
pattern FT1 = BuildFPR 1

-- | Temporary register
pattern FT2 :: FPR
pattern FT2 = BuildFPR 2

-- | Temporary register
pattern FT3 :: FPR
pattern FT3 = BuildFPR 3

-- | Temporary register
pattern FT4 :: FPR
pattern FT4 = BuildFPR 4

-- | Temporary register
pattern FT5 :: FPR
pattern FT5 = BuildFPR 5

-- | Temporary register
pattern FT6 :: FPR
pattern FT6 = BuildFPR 6

-- | Temporary register
pattern FT7 :: FPR
pattern FT7 = BuildFPR 7

-- | Callee-saved register
pattern FS0 :: FPR
pattern FS0 = BuildFPR 8

-- | Callee-saved register
pattern FS1 :: FPR
pattern FS1 = BuildFPR 9

-- | Argument register
pattern FA0 :: FPR
pattern FA0 = BuildFPR 10

-- | Argument register
pattern FA1 :: FPR
pattern FA1 = BuildFPR 11

-- | Argument register
pattern FA2 :: FPR
pattern FA2 = BuildFPR 12

-- | Argument register
pattern FA3 :: FPR
pattern FA3 = BuildFPR 13

-- | Argument register
pattern FA4 :: FPR
pattern FA4 = BuildFPR 14

-- | Argument register
pattern FA5 :: FPR
pattern FA5 = BuildFPR 15

-- | Argument register
pattern FA6 :: FPR
pattern FA6 = BuildFPR 16

-- | Argument register
pattern FA7 :: FPR
pattern FA7 = BuildFPR 17

-- | Callee-saved register
pattern FS2 :: FPR
pattern FS2 = BuildFPR 18

-- | Callee-saved register
pattern FS3 :: FPR
pattern FS3 = BuildFPR 19

-- | Callee-saved register
pattern FS4 :: FPR
pattern FS4 = BuildFPR 20

-- | Callee-saved register
pattern FS5 :: FPR
pattern FS5 = BuildFPR 21

-- | Callee-saved register
pattern FS6 :: FPR
pattern FS6 = BuildFPR 22

-- | Callee-saved register
pattern FS7 :: FPR
pattern FS7 = BuildFPR 23

-- | Callee-saved register
pattern FS8 :: FPR
pattern FS8 = BuildFPR 24

-- | Callee-saved register
pattern FS9 :: FPR
pattern FS9 = BuildFPR 25

-- | Callee-saved register
pattern FS10 :: FPR
pattern FS10 = BuildFPR 26

-- | Callee-saved register
pattern FS11 :: FPR
pattern FS11 = BuildFPR 27

-- | Temporary register
pattern FT8 :: FPR
pattern FT8 = BuildFPR 28

-- | Temporary register
pattern FT9 :: FPR
pattern FT9 = BuildFPR 29

-- | Temporary register
pattern FT10 :: FPR
pattern FT10 = BuildFPR 30

-- | Temporary register
pattern FT11 :: FPR
pattern FT11 = BuildFPR 31

{-# COMPLETE
  FT0, FT1, FT2, FT3, FT4, FT5, FT6, FT7,
  FS0, FS1,
  FA0, FA1, FA2, FA3, FA4, FA5, FA6, FA7,
  FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11,
  FT8, FT9, FT10, FT11 #-}

instance Show FPR where
  show FT0  = "ft0"
  show FT1  = "ft1"
  show FT2  = "ft2"
  show FT3  = "ft3"
  show FT4  = "ft4"
  show FT5  = "ft5"
  show FT6  = "ft6"
  show FT7  = "ft7"
  show FS0  = "fs0"
  show FS1  = "fs1"
  show FA0  = "fa0"
  show FA1  = "fa1"
  show FA2  = "fa2"
  show FA3  = "fa3"
  show FA4  = "fa4"
  show FA5  = "fa5"
  show FA6  = "fa6"
  show FA7  = "fa7"
  show FS2  = "fs2"
  show FS3  = "fs3"
  show FS4  = "fs4"
  show FS5  = "fs5"
  show FS6  = "fs6"
  show FS7  = "fs7"
  show FS8  = "fs8"
  show FS9  = "fs9"
  show FS10 = "fs10"
  show FS11 = "fs11"
  show FT8  = "ft8"
  show FT9  = "ft9"
  show FT10 = "ft10"
  show FT11 = "ft11"

-- | RISC-V register.
data RISCVReg rv tp where
  -- | Program counter.
  PC  :: RISCVReg rv (MT.BVType (G.RVWidth rv))
  -- | General-purpose registers. GPR[0] is not really a register, so
  -- it should never be directly read from or written to.
  RISCV_GPR :: GPR -> RISCVReg rv (MT.BVType (G.RVWidth rv))
  -- | Floating-point registers.
  RISCV_FPR :: FPR -> RISCVReg rv (MT.BVType (G.RVFloatWidth rv))
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

pattern FPR ::
  forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
    G.SizedBV 5 -> RISCVReg rv tp
pattern FPR bv = RISCV_FPR (BuildFPR bv)

-- | Temporary register
pattern FPR_FT0 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT0 = FPR 0

-- | Temporary register
pattern FPR_FT1 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT1 = FPR 1

-- | Temporary register
pattern FPR_FT2 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT2 = FPR 2

-- | Temporary register
pattern FPR_FT3 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT3 = FPR 3

-- | Temporary register
pattern FPR_FT4 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT4 = FPR 4

-- | Temporary register
pattern FPR_FT5 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT5 = FPR 5

-- | Temporary register
pattern FPR_FT6 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT6 = FPR 6

-- | Temporary register
pattern FPR_FT7 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT7 = FPR 7

-- | Callee-saved register
pattern FPR_FS0 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS0 = FPR 8

-- | Callee-saved register
pattern FPR_FS1 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS1 = FPR 9

-- | Argument register
pattern FPR_FA0 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FA0 = FPR 10

-- | Argument register
pattern FPR_FA1 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FA1 = FPR 11

-- | Argument register
pattern FPR_FA2 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FA2 = FPR 12

-- | Argument register
pattern FPR_FA3 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FA3 = FPR 13

-- | Argument register
pattern FPR_FA4 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FA4 = FPR 14

-- | Argument register
pattern FPR_FA5 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FA5 = FPR 15

-- | Argument register
pattern FPR_FA6 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FA6 = FPR 16

-- | Argument register
pattern FPR_FA7 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FA7 = FPR 17

-- | Callee-saved register
pattern FPR_FS2 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS2 = FPR 18

-- | Callee-saved register
pattern FPR_FS3 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS3 = FPR 19

-- | Callee-saved register
pattern FPR_FS4 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS4 = FPR 20

-- | Callee-saved register
pattern FPR_FS5 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS5 = FPR 21

-- | Callee-saved register
pattern FPR_FS6 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS6 = FPR 22

-- | Callee-saved register
pattern FPR_FS7 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS7 = FPR 23

-- | Callee-saved register
pattern FPR_FS8 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS8 = FPR 24

-- | Callee-saved register
pattern FPR_FS9 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FS9 = FPR 25

-- | Callee-saved register
pattern FPR_FS10 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                    RISCVReg rv tp
pattern FPR_FS10 = FPR 26

-- | Callee-saved register
pattern FPR_FS11 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                    RISCVReg rv tp
pattern FPR_FS11 = FPR 27

-- | Temporary register
pattern FPR_FT8 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT8 = FPR 28

-- | Temporary register
pattern FPR_FT9 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                   RISCVReg rv tp
pattern FPR_FT9 = FPR 29

-- | Temporary register
pattern FPR_FT10 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                    RISCVReg rv tp
pattern FPR_FT10 = FPR 30

-- | Temporary register
pattern FPR_FT11 :: forall rv tp . () => (tp ~ 'MT.BVType (G.RVFloatWidth rv)) =>
                    RISCVReg rv tp
pattern FPR_FT11 = FPR 31

instance Show (RISCVReg rv tp) where
  show PC = "pc"
  show (RISCV_GPR gpr) = show gpr
  show (RISCV_FPR fpr) = show fpr
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
  typeRepr (RISCV_FPR _) = MT.BVTypeRepr knownNat
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
