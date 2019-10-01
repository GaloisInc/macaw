{-
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This contains a type for modeling the X87 control register
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.X86.X87ControlReg
  ( X87_ControlReg
  , x87_IM
  , x87_DM
  , x87_ZM
  , x87_OM
  , x87_UM
  , x87_PM
  , x87_PC
  , x87_RC
  , x87_X
  , x87ControlRegWidthIsPos
  ) where

import           Data.Macaw.Types
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr

-- | This is one of the fields in the x87 FPU control word.
--
-- The fields indicate the index of the least-significant bit that is part of
-- the field, and the number of bits in the field.
data X87_ControlReg w = (1 <= w) => X87_ControlReg !Int !(NatRepr w)

instance TestEquality X87_ControlReg where
  testEquality (X87_ControlReg xi xw) (X87_ControlReg yi yw) =
    if xi == yi then
      testEquality xw yw
     else
      Nothing

instance OrdF X87_ControlReg where
  compareF (X87_ControlReg xi xw) (X87_ControlReg yi yw) =
    case compare xi yi of
      LT -> LTF
      GT -> GTF
      EQ -> compareF xw yw

instance HasRepr X87_ControlReg NatRepr where
  typeRepr (X87_ControlReg _ w) = w

instance Show (X87_ControlReg w) where
  show (X87_ControlReg i _) =
    case i of
      0 -> "im"
      1 -> "dm"
      2 -> "zm"
      3 -> "om"
      4 -> "um"
      5 -> "pm"
      8 -> "pc"
      10 -> "rc"
      12 -> "x"
      _  -> "reserved"

x87_IM :: X87_ControlReg 1
x87_IM = X87_ControlReg  0 n1

x87_DM :: X87_ControlReg 1
x87_DM = X87_ControlReg  1 n1

x87_ZM :: X87_ControlReg 1
x87_ZM = X87_ControlReg  2 n1

x87_OM :: X87_ControlReg 1
x87_OM = X87_ControlReg  3 n1

x87_UM :: X87_ControlReg 1
x87_UM = X87_ControlReg  4 n1

x87_PM :: X87_ControlReg 1
x87_PM = X87_ControlReg  5 n1

-- | X87 precision control field.
--
-- Values are:
-- 00 Single Precision (24 bits)
-- 01 Reserved
-- 10 Double Precision (53 bits)
-- 11 Double Extended Precision (64 bits)
x87_PC :: X87_ControlReg 2
x87_PC = X87_ControlReg  8 knownNat

-- | X87 rounding control field.  Values are:
--
-- 00 Round to nearest (even)
-- Rounded result is the closest to the infinitely precise result. If two
-- values are equally close, the result is the even value (that is, the one
-- with the least-significant bit of zero). Default
--
-- 01 Round down (toward −∞)
-- Rounded result is closest to but no greater than the infinitely precise result.
--
-- 10 Round up (toward +∞)
-- Rounded result is closest to but no less than the infinitely precise result.
--
-- 11 Round toward zero (Truncate)
-- Rounded result is closest to but no greater in absolute value than the
-- infinitely precise result.
x87_RC :: X87_ControlReg 2
x87_RC = X87_ControlReg 10 knownNat

x87_X :: X87_ControlReg 1
x87_X  = X87_ControlReg 12 n1


x87ControlRegWidthIsPos :: X87_ControlReg w -> LeqProof 1 w
x87ControlRegWidthIsPos (X87_ControlReg _ _) = LeqProof
