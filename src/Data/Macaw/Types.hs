-- |
-- Module           : Reopt.Semantics.Types
-- Description      : This defines the types of machine words
-- Copyright        : (c) Galois, Inc 2015
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- The type of machine words, including bit vectors and floating point
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
module Data.Macaw.Types
  ( module Data.Macaw.Types -- export everything
  , GHC.TypeLits.Nat
  , Data.Parameterized.NatRepr.NatRepr(..)
  , Data.Parameterized.NatRepr.knownNat
  ) where

import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import GHC.TypeLits
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

-- FIXME: move
n0 :: NatRepr 0
n0 = knownNat

n1 :: NatRepr 1
n1 = knownNat

n4 :: NatRepr 4
n4 = knownNat

n8 :: NatRepr 8
n8 = knownNat

n16 :: NatRepr 16
n16 = knownNat

n32 :: NatRepr 32
n32 = knownNat

n64 :: NatRepr 64
n64 = knownNat

n80 :: NatRepr 80
n80 = knownNat

n128 :: NatRepr 128
n128 = knownNat

------------------------------------------------------------------------
-- Type

data Type
  = -- | A bitvector with the given number of bits.
    BVType Nat
    -- | 64 bit binary IEE754
  | DoubleFloat
    -- | 32 bit binary IEE754
  | SingleFloat
    -- | X86 80-bit extended floats
  | X86_80Float
    -- | 128 bit binary IEE754
  | QuadFloat
    --  | 16 bit binary IEE754
  | HalfFloat

-- Return number of bytes in the type.
type family TypeBytes (tp :: Type) :: Nat where
  TypeBytes (BVType  8) =  1
  TypeBytes (BVType 16) =  2
  TypeBytes (BVType 32) =  4
  TypeBytes (BVType 64) =  8
  TypeBytes HalfFloat   =  2
  TypeBytes SingleFloat =  4
  TypeBytes DoubleFloat =  8
  TypeBytes QuadFloat   = 16
  TypeBytes X86_80Float = 10

-- Return number of bits in the type.
type family TypeBits (tp :: Type) :: Nat where
  TypeBits (BVType n)  = n
  TypeBits HalfFloat   = 16
  TypeBits SingleFloat = 32
  TypeBits DoubleFloat = 64
  TypeBits QuadFloat   = 128
  TypeBits X86_80Float = 80

type FloatType tp = BVType (8 * TypeBytes tp)

type BVType = 'BVType

type BoolType   = BVType 1

-- | A runtime representation of @Type@ for case matching purposes.
data TypeRepr (tp :: Type) where
  BVTypeRepr :: !(NatRepr n) -> TypeRepr (BVType n)

type_width :: TypeRepr (BVType n) -> NatRepr n
type_width (BVTypeRepr n) = n

instance TestEquality TypeRepr where
  testEquality (BVTypeRepr m) (BVTypeRepr n) = do
    Refl <- testEquality m n
    return Refl

instance OrdF TypeRepr where
  compareF (BVTypeRepr m) (BVTypeRepr n) = do
    case compareF m n of
      LTF -> LTF
      EQF -> EQF
      GTF -> GTF

class KnownType tp where
  knownType :: TypeRepr tp

instance KnownNat n => KnownType (BVType n) where
  knownType = BVTypeRepr knownNat

------------------------------------------------------------------------
-- Floating point sizes

type SingleFloat = 'SingleFloat
type DoubleFloat = 'DoubleFloat
type X86_80Float = 'X86_80Float
type QuadFloat = 'QuadFloat
type HalfFloat = 'HalfFloat

data FloatInfoRepr (flt::Type) where
  DoubleFloatRepr       :: FloatInfoRepr DoubleFloat
  SingleFloatRepr       :: FloatInfoRepr SingleFloat
  X86_80FloatRepr       :: FloatInfoRepr X86_80Float
  QuadFloatRepr         :: FloatInfoRepr QuadFloat
  HalfFloatRepr         :: FloatInfoRepr HalfFloat

deriving instance Show (FloatInfoRepr tp)

instance TestEquality FloatInfoRepr where
  testEquality x y = orderingF_refl (compareF x y)

instance OrdF FloatInfoRepr where
  compareF DoubleFloatRepr DoubleFloatRepr = EQF
  compareF DoubleFloatRepr _               = LTF
  compareF _               DoubleFloatRepr = GTF

  compareF SingleFloatRepr SingleFloatRepr = EQF
  compareF SingleFloatRepr _               = LTF
  compareF _               SingleFloatRepr = GTF

  compareF X86_80FloatRepr X86_80FloatRepr = EQF
  compareF X86_80FloatRepr _               = LTF
  compareF _               X86_80FloatRepr = GTF

  compareF QuadFloatRepr   QuadFloatRepr   = EQF
  compareF QuadFloatRepr   _               = LTF
  compareF _               QuadFloatRepr   = GTF

  compareF HalfFloatRepr   HalfFloatRepr   = EQF

instance Pretty (FloatInfoRepr flt) where
  pretty DoubleFloatRepr = text "double"
  pretty SingleFloatRepr = text "single"
  pretty X86_80FloatRepr = text "x87_80"
  pretty QuadFloatRepr   = text "quad"
  pretty HalfFloatRepr   = text "half"


floatInfoBytes :: FloatInfoRepr flt -> NatRepr (TypeBytes flt)
floatInfoBytes fir =
  case fir of
    HalfFloatRepr         -> knownNat
    SingleFloatRepr       -> knownNat
    DoubleFloatRepr       -> knownNat
    QuadFloatRepr         -> knownNat
    X86_80FloatRepr       -> knownNat

floatInfoBits :: FloatInfoRepr flt -> NatRepr (8 * TypeBytes flt)
floatInfoBits fir = natMultiply (knownNat :: NatRepr 8) (floatInfoBytes fir)

floatTypeRepr :: FloatInfoRepr flt -> TypeRepr (BVType (8 * TypeBytes flt))
floatTypeRepr fir = BVTypeRepr (floatInfoBits fir)

------------------------------------------------------------------------
--

-- | A multi-parameter type class that allows one to represent that a
-- parameterized type value has some representative type such as a TypeRepr.
class HasRepr (f :: k -> *) (v :: k -> *)  | f -> v where
  typeRepr :: f tp -> v tp
