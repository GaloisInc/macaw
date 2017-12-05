{-|
Copyright        : (c) Galois, Inc 2015
Maintainer       : Joe Hendrix <jhendrix@galois.com>

The type of machine words, including bit vectors and floating point
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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
import Data.Parameterized.TraversableFC
import GHC.TypeLits
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.TypedList (TList)
import qualified Data.Macaw.TypedList as TList

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
    -- | 16 bit binary IEE754
  | HalfFloat
    -- | A Boolean value
  | BoolType
    -- | A tuple of types
  | TupleType [Type]


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

type BoolType = 'BoolType

-- | A runtime representation of @Type@ for case matching purposes.
data TypeRepr (tp :: Type) where
  BoolTypeRepr :: TypeRepr BoolType
  BVTypeRepr :: (1 <= n) => !(NatRepr n) -> TypeRepr (BVType n)
  TupleTypeRepr :: !(TList TypeRepr ctx) -> TypeRepr (TupleType ctx)

type_width :: TypeRepr (BVType n) -> NatRepr n
type_width (BVTypeRepr n) = n

instance TestEquality TypeRepr where
  testEquality BoolTypeRepr BoolTypeRepr = do
    return Refl
  testEquality (BVTypeRepr m) (BVTypeRepr n) = do
    Refl <- testEquality m n
    return Refl
  testEquality _ _ = Nothing

instance OrdF TypeRepr where
  compareF BoolTypeRepr BoolTypeRepr = EQF
  compareF BoolTypeRepr _ = LTF
  compareF _ BoolTypeRepr = GTF
  compareF (BVTypeRepr m) (BVTypeRepr n) = do
    lexCompareF m n EQF
  compareF BVTypeRepr{} _ = LTF
  compareF _ BVTypeRepr{} = GTF
  compareF (TupleTypeRepr x) (TupleTypeRepr y) =
    lexCompareF x y EQF

instance Show (TypeRepr tp) where
  show BoolTypeRepr = "bool"
  show (BVTypeRepr w) = "[" ++ show w ++ "]"
  show (TupleTypeRepr TList.Empty) = "()"
  show (TupleTypeRepr (h TList.:| z)) =
    "(" ++ show h ++ foldrFC (\tp r -> "," ++ show tp ++ r) ")" z

class KnownType tp where
  knownType :: TypeRepr tp

class KnownTypeList l where
  knownTypeList :: TList TypeRepr l

instance KnownTypeList '[] where
  knownTypeList = TList.Empty

instance (KnownType h, KnownTypeList r) => KnownTypeList (h : r) where
  knownTypeList = knownType TList.:| knownTypeList


instance KnownType BoolType where
  knownType = BoolTypeRepr

instance (KnownNat n, 1 <= n) => KnownType (BVType n) where
  knownType = BVTypeRepr knownNat

instance (KnownTypeList l) => KnownType (TupleType l) where
  knownType = TupleTypeRepr knownTypeList

------------------------------------------------------------------------
-- Floating point sizes

type SingleFloat = 'SingleFloat
type DoubleFloat = 'DoubleFloat
type X86_80Float = 'X86_80Float
type QuadFloat   = 'QuadFloat
type HalfFloat   = 'HalfFloat

data FloatInfoRepr (flt::Type) where
  DoubleFloatRepr :: FloatInfoRepr DoubleFloat
  SingleFloatRepr :: FloatInfoRepr SingleFloat
  X86_80FloatRepr :: FloatInfoRepr X86_80Float
  QuadFloatRepr   :: FloatInfoRepr QuadFloat
  HalfFloatRepr   :: FloatInfoRepr HalfFloat

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

floatInfoBytesIsPos :: FloatInfoRepr flt -> LeqProof 1 (TypeBytes flt)
floatInfoBytesIsPos fir =
  case fir of
    HalfFloatRepr         -> LeqProof
    SingleFloatRepr       -> LeqProof
    DoubleFloatRepr       -> LeqProof
    QuadFloatRepr         -> LeqProof
    X86_80FloatRepr       -> LeqProof


floatInfoBits :: FloatInfoRepr flt -> NatRepr (8 * TypeBytes flt)
floatInfoBits fir = natMultiply (knownNat :: NatRepr 8) (floatInfoBytes fir)

floatTypeRepr :: FloatInfoRepr flt -> TypeRepr (BVType (8 * TypeBytes flt))
floatTypeRepr fir =
  case fir of
    HalfFloatRepr         -> knownType
    SingleFloatRepr       -> knownType
    DoubleFloatRepr       -> knownType
    QuadFloatRepr         -> knownType
    X86_80FloatRepr       -> knownType

floatInfoBitsIsPos :: FloatInfoRepr flt -> LeqProof 1 (8 * TypeBytes flt)
floatInfoBitsIsPos fir =
  case fir of
    HalfFloatRepr         -> LeqProof
    SingleFloatRepr       -> LeqProof
    DoubleFloatRepr       -> LeqProof
    QuadFloatRepr         -> LeqProof
    X86_80FloatRepr       -> LeqProof

------------------------------------------------------------------------
--

-- | A multi-parameter type class that allows one to represent that a
-- parameterized type value has some representative type such as a TypeRepr.
class HasRepr (f :: k -> *) (v :: k -> *) | f -> v where
  typeRepr :: f tp -> v tp

typeWidth :: HasRepr f TypeRepr => f (BVType w) -> NatRepr w
typeWidth x =
  case typeRepr x of
    BVTypeRepr w -> w
