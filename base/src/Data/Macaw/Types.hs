{-|
Copyright        : (c) Galois, Inc 2015
Maintainer       : Joe Hendrix <jhendrix@galois.com>

The type of machine words, including bit vectors and floating point
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Types
  ( module Data.Macaw.Types -- export everything
  , GHC.TypeLits.Nat
  , Data.Parameterized.NatRepr.NatRepr(..)
  , Data.Parameterized.NatRepr.knownNat
  ) where

import qualified Data.Kind as Kind
import           Data.Parameterized.Classes
import qualified Data.Parameterized.List as P
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           GHC.TypeLits
import qualified Language.Haskell.TH.Syntax as TH
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

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

n256 :: NatRepr 256
n256 = knownNat

n512 :: NatRepr 512
n512 = knownNat

------------------------------------------------------------------------
-- Floating point sizes

data FloatInfo
  = HalfFloat   -- ^ 16 bit binary IEE754
  | SingleFloat -- ^ 32 bit binary IEE754
  | DoubleFloat -- ^ 64 bit binary IEE754
  | QuadFloat   -- ^ 128 bit binary IEE754
  | X86_80Float -- ^ X86 80-bit extended floats

type HalfFloat   = 'HalfFloat
type SingleFloat = 'SingleFloat
type DoubleFloat = 'DoubleFloat
type QuadFloat   = 'QuadFloat
type X86_80Float = 'X86_80Float

data FloatInfoRepr (fi :: FloatInfo) where
  HalfFloatRepr   :: FloatInfoRepr HalfFloat
  SingleFloatRepr :: FloatInfoRepr SingleFloat
  DoubleFloatRepr :: FloatInfoRepr DoubleFloat
  QuadFloatRepr   :: FloatInfoRepr QuadFloat
  X86_80FloatRepr :: FloatInfoRepr X86_80Float

instance KnownRepr FloatInfoRepr HalfFloat where
  knownRepr = HalfFloatRepr
instance KnownRepr FloatInfoRepr SingleFloat where
  knownRepr = SingleFloatRepr
instance KnownRepr FloatInfoRepr DoubleFloat where
  knownRepr = DoubleFloatRepr
instance KnownRepr FloatInfoRepr QuadFloat where
  knownRepr = QuadFloatRepr
instance KnownRepr FloatInfoRepr X86_80Float where
  knownRepr = X86_80FloatRepr

instance Show (FloatInfoRepr fi) where
  show HalfFloatRepr   = "half"
  show SingleFloatRepr = "single"
  show DoubleFloatRepr = "double"
  show QuadFloatRepr   = "quad"
  show X86_80FloatRepr = "x87_80"

instance Pretty (FloatInfoRepr fi) where
  pretty = text . show

deriving instance TH.Lift (FloatInfoRepr fi)

type family FloatInfoBytes (fi :: FloatInfo) :: Nat where
  FloatInfoBytes HalfFloat   = 2
  FloatInfoBytes SingleFloat = 4
  FloatInfoBytes DoubleFloat = 8
  FloatInfoBytes QuadFloat   = 16
  FloatInfoBytes X86_80Float = 10

floatInfoBytes :: FloatInfoRepr fi -> NatRepr (FloatInfoBytes fi)
floatInfoBytes = \case
  HalfFloatRepr   -> knownNat
  SingleFloatRepr -> knownNat
  DoubleFloatRepr -> knownNat
  QuadFloatRepr   -> knownNat
  X86_80FloatRepr -> knownNat

floatInfoBytesIsPos :: FloatInfoRepr fi -> LeqProof 1 (FloatInfoBytes fi)
floatInfoBytesIsPos = \case
  HalfFloatRepr   -> LeqProof
  SingleFloatRepr -> LeqProof
  DoubleFloatRepr -> LeqProof
  QuadFloatRepr   -> LeqProof
  X86_80FloatRepr -> LeqProof

type FloatInfoBits (fi :: FloatInfo) = 8 * FloatInfoBytes fi

floatInfoBits :: FloatInfoRepr fi -> NatRepr (FloatInfoBits fi)
floatInfoBits = natMultiply (knownNat @8) . floatInfoBytes

floatInfoBitsIsPos :: FloatInfoRepr fi -> LeqProof 1 (FloatInfoBits fi)
floatInfoBitsIsPos = \case
  HalfFloatRepr   -> LeqProof
  SingleFloatRepr -> LeqProof
  DoubleFloatRepr -> LeqProof
  QuadFloatRepr   -> LeqProof
  X86_80FloatRepr -> LeqProof

$(return [])

------------------------------------------------------------------------
-- Type

data Type
  = -- | A bitvector with the given number of bits.
    BVType Nat
    -- | A floating point in the given format.
  | FloatType FloatInfo
    -- | A Boolean value
  | BoolType
    -- | A tuple of types
  | TupleType [Type]
    -- | A vector of types
  | VecType Nat Type


-- Return number of bytes in the type.
type family TypeBytes (tp :: Type) :: Nat where
  TypeBytes (BVType  8) = 1
  TypeBytes (BVType 16) = 2
  TypeBytes (BVType 32) = 4
  TypeBytes (BVType 64) = 8
  TypeBytes (FloatType fi) = FloatInfoBytes fi
  TypeBytes (VecType n tp) = n * TypeBytes tp

-- Return number of bits in the type.
type family TypeBits (tp :: Type) :: Nat where
  TypeBits (BVType n) = n
  TypeBits (FloatType fi) = 8 * FloatInfoBytes fi

type BVType = 'BVType

type FloatType = 'FloatType

type BoolType = 'BoolType

type TupleType = 'TupleType

-- | The bitvector associated with the given floating-point format.
type FloatBVType (fi :: FloatInfo) = BVType (FloatInfoBits fi)

$(pure [])


-- | A runtime representation of @Type@ for case matching purposes.
data TypeRepr (tp :: Type) where
  BoolTypeRepr :: TypeRepr BoolType
  BVTypeRepr :: (1 <= n) => !(NatRepr n) -> TypeRepr (BVType n)
  FloatTypeRepr :: !(FloatInfoRepr fi) -> TypeRepr (FloatType fi)
  TupleTypeRepr :: !(P.List TypeRepr ctx) -> TypeRepr (TupleType ctx)
  VectorTypeRepr :: NatRepr n -> TypeRepr tp -> TypeRepr (VecType n tp)

type_width :: TypeRepr (BVType n) -> NatRepr n
type_width (BVTypeRepr n) = n

instance Show (TypeRepr tp) where
  show BoolTypeRepr = "bool"
  show (BVTypeRepr w) = "[" ++ show w ++ "]"
  show (FloatTypeRepr fi) = show fi ++ "_float"
  show (TupleTypeRepr P.Nil) = "()"
  show (TupleTypeRepr (h P.:< z)) =
    "(" ++ show h ++ foldrFC (\tp r -> "," ++ show tp ++ r) ")" z
  show (VectorTypeRepr c tp) = "(vec " ++ show c ++ " " ++ show tp ++ ")"

instance ShowF TypeRepr

instance KnownRepr TypeRepr BoolType where
  knownRepr = BoolTypeRepr

instance (KnownNat n, 1 <= n) => KnownRepr TypeRepr (BVType n) where
  knownRepr = BVTypeRepr knownNat

instance (KnownRepr FloatInfoRepr fi) => KnownRepr TypeRepr (FloatType fi) where
  knownRepr = FloatTypeRepr knownRepr

instance (KnownRepr (P.List TypeRepr) l) => KnownRepr TypeRepr  (TupleType l) where
  knownRepr = TupleTypeRepr knownRepr

$(pure [])

instance TestEquality TypeRepr where
  testEquality = $(structuralTypeEquality [t|TypeRepr|]
    [ (ConType [t|NatRepr|]       `TypeApp` AnyType, [|testEquality|])
    , (ConType [t|TypeRepr|]      `TypeApp` AnyType, [|testEquality|])
    , (ConType [t|FloatInfoRepr|] `TypeApp` AnyType, [|testEquality|])
    , ( ConType [t|P.List|] `TypeApp` AnyType `TypeApp` AnyType
      , [|testEquality|]
      )
    ])

instance OrdF TypeRepr where
  compareF = $(structuralTypeOrd [t|TypeRepr|]
    [ (ConType [t|NatRepr|]       `TypeApp` AnyType, [|compareF|])
    , (ConType [t|TypeRepr|]      `TypeApp` AnyType, [|compareF|])
    , (ConType [t|FloatInfoRepr|] `TypeApp` AnyType, [|compareF|])
    , (ConType [t|P.List|] `TypeApp` AnyType `TypeApp` AnyType, [|compareF|])
    ])

instance TestEquality FloatInfoRepr where
  testEquality = $(structuralTypeEquality [t|FloatInfoRepr|] [])
instance OrdF FloatInfoRepr where
  compareF = $(structuralTypeOrd [t|FloatInfoRepr|] [])

floatBVTypeRepr :: FloatInfoRepr fi -> TypeRepr (FloatBVType fi)
floatBVTypeRepr fi | LeqProof <- floatInfoBitsIsPos fi =
  BVTypeRepr $ floatInfoBits fi

------------------------------------------------------------------------
--

-- | A multi-parameter type class that allows one to represent that a
-- parameterized type value has some representative type such as a TypeRepr.
class HasRepr (f :: k -> Kind.Type) (v :: k -> Kind.Type) | f -> v where
  typeRepr :: f tp -> v tp

typeWidth :: HasRepr f TypeRepr => f (BVType w) -> NatRepr w
typeWidth x =
  case typeRepr x of
    BVTypeRepr w -> w
