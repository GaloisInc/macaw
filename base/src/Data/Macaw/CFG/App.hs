{-|
Copyright        : (c) Galois, Inc 2015-2018
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines a data type `App` for representing operations that can be
applied to a range of values.  We call it an `App` because it
represents an application of an operation.  In mathematics, we would
probably call it a signature.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.CFG.App
  ( App(..)
  , ppApp
  , ppAppA
  ) where

import qualified Data.Kind as Kind
import           Control.Monad.Identity
import           Data.Parameterized.Classes
import qualified Data.Parameterized.List as P
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Data.Macaw.Types
import           Data.Macaw.Utils.Pretty

-----------------------------------------------------------------------
-- App

-- | This datatype defines operations used on multiple architectures.
--
-- These operations are all total functions.  Different architecture tend to have
-- different ways of raising signals or exceptions, and so partial functions are
-- all architecture specific.
data App (f :: Type -> Kind.Type) (tp :: Type) where

  -- Compare for equality.
  Eq :: !(f tp) -> !(f tp) -> App f BoolType

  Mux :: !(TypeRepr tp) -> !(f BoolType) -> !(f tp) -> !(f tp) -> App f tp

  -- | Extract the value out of a tuple.
  TupleField :: !(P.List TypeRepr l) -> !(f (TupleType l)) -> !(P.Index l r) -> App f r

  ----------------------------------------------------------------------
  -- Boolean operations

  AndApp :: !(f BoolType) -> !(f BoolType) -> App f BoolType
  OrApp  :: !(f BoolType) -> !(f BoolType) -> App f BoolType
  NotApp :: !(f BoolType) -> App f BoolType
  XorApp  :: !(f BoolType) -> !(f BoolType) -> App f BoolType

  ----------------------------------------------------------------------
  -- Operations related to concatenating and extending bitvectors.

  -- | Given a @m@-bit bitvector and a natural number @n@ less than @m@, this returns
  -- the bitvector with the @n@ least significant bits.
  Trunc :: (1 <= n, n+1 <= m) => !(f (BVType m)) -> !(NatRepr n) -> App f (BVType n)
  -- | Given a @m@-bit bitvector @x@ and a natural number @n@ greater than @m@, this returns
  -- the bitvector with the same @m@ least signficant bits, and where the new bits are
  -- the same as the most significant bit in @x@.
  SExt :: (1 <= m, m+1 <= n, 1 <= n) => f (BVType m) -> NatRepr n -> App f (BVType n)
  -- | Given a @m@-bit bitvector @x@ and a natural number @n@ greater than @m@, this returns
  -- the bitvector with the same @m@ least signficant bits, and where the new bits are
  -- all @false@.
  UExt :: (1 <= m, m+1 <= n, 1 <= n) => f (BVType m) -> NatRepr n -> App f (BVType n)

  ----------------------------------------------------------------------
  -- Bitvector operations

  -- | @BVAdd w x y@ denotes @x + y@.
  BVAdd :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)

  -- | @BVAdc w x y c@ denotes @x + y + (c ? 1 : 0)@.
  BVAdc :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> !(f BoolType) -> App f (BVType n)

  -- | @BVSub w x y@ denotes @x - y@.
  BVSub :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)

  -- | @BVSbb w x y b@ denotes @(x - y) - (b ? 1 : 0)@.
  BVSbb :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> !(f BoolType) -> App f (BVType n)

  -- Multiply two numbers
  BVMul :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)

  -- Unsigned less than or equal.
  BVUnsignedLe :: (1 <= n) => !(f (BVType n)) -> !(f (BVType n)) -> App f BoolType

  -- Unsigned less than.
  BVUnsignedLt :: (1 <= n) => !(f (BVType n)) -> !(f (BVType n)) -> App f BoolType

  -- Signed less than or equal.
  BVSignedLe :: (1 <= n) => !(f (BVType n)) -> !(f (BVType n)) -> App f BoolType

  -- Signed less than
  BVSignedLt :: (1 <= n) => !(f (BVType n)) -> !(f (BVType n)) -> App f BoolType

  -- @BVTestBit x i@ returns true iff bit @i@ of @x@ is true.
  -- 0 is the index of the least-significant bit.
  --
  -- If the value is larger than the width of n, then the result is false.
  BVTestBit :: (1 <= n) => !(f (BVType n)) -> !(f (BVType n)) -> App f BoolType

  -- Bitwise complement
  BVComplement :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> App f (BVType n)
  -- Bitwise and
  BVAnd :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)
  -- Bitwise or
  BVOr  :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)
  -- Exclusive or
  BVXor :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)

  -- Logical left shift (x * 2 ^ n)
  BVShl :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)
  -- Logical right shift (x / 2 ^ n)
  BVShr :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)
  -- Arithmetic right shift (x / 2 ^ n)
  BVSar :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)

  -- | Add two values and a carry bit to determine if they have an
  -- unsigned overflow.
  --
  -- This is the sum of three three values cannot be represented as an
  -- unsigned number.
  UadcOverflows :: (1 <= n)
                => !(f (BVType n))
                -> !(f (BVType n))
                -> !(f BoolType)
                -> App f BoolType

  -- | Add two values and a carry bit to determine if they have a
  -- signed overflow.
  --
  -- @SadcOverflows  w x y c@ should be true iff the result
  -- @toNat x + toNat y + (c ? 1 : 0)@ is greater than @2^w-1@.
  SadcOverflows :: (1 <= n)
                => !(f (BVType n))
                -> !(f (BVType n))
                -> !(f BoolType)
                -> App f BoolType

  -- | Unsigned subtract with borrow overflow
  --
  -- @UsbbOverflows w x y c@ should be true iff the result
  -- @(toNat x - toNat y) - (c ? 1 : 0)@ is non-negative.
  -- Since everything is
  -- unsigned, this is equivalent to @x unsignedLt (y + (c ? 1 : 0)@.
  UsbbOverflows :: (1 <= n)
                => !(f (BVType n))
                -> !(f (BVType n))
                -> !(f BoolType)
                -> App f BoolType

  -- | Signed subtract with borrow overflow.
  --
  -- @SsbbOverflows w x y c@ should be true iff the result
  -- @(toInt x - toInt y) - (c ? 1 : 0)@ is not between @-2^(w-1)@ and @2^(w-1)-1@.
  -- An equivalent way to express this is that x and y should have opposite signs and
  -- the sign of the result should differ from the sign of x.
  SsbbOverflows :: (1 <= n)
                => !(f (BVType n))
                -> !(f (BVType n))
                -> !(f BoolType)
                -> App f BoolType

  -- | This returns the number of true bits in the input.
  PopCount :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> App f (BVType n)

  -- | Reverse the bytes in a bitvector expression.
  ReverseBytes :: (1 <= n) => !(NatRepr n) -> !(f (BVType (8*n))) -> App f (BVType (8*n))

  -- | bsf "bit scan forward" returns the index of the
  -- least-significant bit that is 1.  An equivalent way of stating
  -- this is that it returns the number zero-bits starting from the
  -- least significant bit.  This returns n if the value is zero.
  Bsf :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> App f (BVType n)

  -- | bsr "bit scan reverse" returns the index of the
  -- most-significant bit that is 1.  An equivalent way of stating
  -- this is that it returns the number zero-bits starting from
  -- the most-significant bit location.  This returns n if the
  -- value is zero.
  Bsr :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> App f (BVType n)

-----------------------------------------------------------------------
-- App utilities

-- Force app to be in template-haskell context.
$(pure [])

instance TestEquality f => Eq (App f tp) where
  (==) = \x y -> isJust (testEquality x y)

instance TestEquality f => TestEquality (App f) where
  testEquality = $(structuralTypeEquality [t|App|]
                   [ (DataArg 0                  `TypeApp` AnyType, [|testEquality|])
                   , (ConType [t|NatRepr|]       `TypeApp` AnyType, [|testEquality|])
                   , (ConType [t|FloatInfoRepr|] `TypeApp` AnyType, [|testEquality|])
                   , (ConType [t|TypeRepr|]      `TypeApp` AnyType, [|testEquality|])
                   , (ConType [t|P.List|] `TypeApp` AnyType `TypeApp` AnyType,
                      [|testEquality|])
                   , (ConType [t|P.Index|] `TypeApp` AnyType `TypeApp` AnyType,
                      [|testEquality|])
                   ]
                  )

instance OrdF f => OrdF (App f) where
  compareF = $(structuralTypeOrd [t|App|]
                   [ (DataArg 0                  `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|NatRepr|]       `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|FloatInfoRepr|] `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|TypeRepr|]      `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|P.List|] `TypeApp` ConType [t|TypeRepr|] `TypeApp` AnyType,
                      [|compareF|])
                   , (ConType [t|P.Index|] `TypeApp` AnyType `TypeApp` AnyType,
                      [|compareF|])
                   ]
              )

instance OrdF f => Ord (App f tp) where
  compare a b =
    case compareF a b of
      LTF -> LT
      EQF -> EQ
      GTF -> GT

instance FunctorFC App where
  fmapFC = fmapFCDefault

instance FoldableFC App where
  foldMapFC = foldMapFCDefault

instance TraversableFC App where
  traverseFC = $(structuralTraversal [t|App|] [])

------------------------------------------------------------------------
-- App pretty printing


prettyPure :: (Applicative m, Pretty v) => v -> m Doc
prettyPure = pure . pretty

-- | Pretty print an 'App' as an expression using the given function
-- for printing arguments.
ppAppA :: Applicative m
      => (forall u . f u -> m Doc)
      -> App f tp
      -> m Doc
ppAppA pp a0 =
  case a0 of
    Mux _ c x y -> sexprA "mux" [ pp c, pp x, pp y ]
    Trunc x w -> sexprA "trunc" [ pp x, ppNat w ]
    TupleField _ x i -> sexprA "tuple_field" [ pp x, prettyPure (P.indexValue i) ]
    SExt x w -> sexprA "sext" [ pp x, ppNat w ]
    UExt x w -> sexprA "uext" [ pp x, ppNat w ]
    AndApp x y -> sexprA "and" [ pp x, pp y ]
    OrApp  x y -> sexprA "or"  [ pp x, pp y ]
    NotApp x   -> sexprA "not" [ pp x ]
    XorApp  x y -> sexprA "xor"  [ pp x, pp y ]
    BVAdd _ x y   -> sexprA "bv_add" [ pp x, pp y ]
    BVAdc _ x y c -> sexprA "bv_adc" [ pp x, pp y, pp c ]
    BVSub _ x y -> sexprA "bv_sub" [ pp x, pp y ]
    BVSbb _ x y b -> sexprA "bv_sbb" [ pp x, pp y, pp b ]
    BVMul _ x y -> sexprA "bv_mul" [ pp x, pp y ]
    BVUnsignedLt x y  -> sexprA "bv_ult"  [ pp x, pp y ]
    BVUnsignedLe x y  -> sexprA "bv_ule"  [ pp x, pp y ]
    BVSignedLt x y    -> sexprA "bv_slt"  [ pp x, pp y ]
    BVSignedLe x y    -> sexprA "bv_sle"  [ pp x, pp y ]
    BVTestBit x i -> sexprA "bv_testbit" [ pp x, pp i]
    BVComplement _ x -> sexprA "bv_complement" [ pp x ]
    BVAnd _ x y -> sexprA "bv_and" [ pp x, pp y ]
    BVOr  _ x y -> sexprA "bv_or"  [ pp x, pp y ]
    BVXor _ x y -> sexprA "bv_xor" [ pp x, pp y ]
    BVShl _ x y -> sexprA "bv_shl" [ pp x, pp y ]
    BVShr _ x y -> sexprA "bv_shr" [ pp x, pp y ]
    BVSar _ x y -> sexprA "bv_sar" [ pp x, pp y ]
    Eq x y      -> sexprA "eq" [ pp x, pp y ]
    PopCount _ x -> sexprA "popcount" [ pp x ]
    ReverseBytes _ x -> sexprA "reverse_bytes" [ pp x ]
    UadcOverflows x y c -> sexprA "uadc_overflows" [ pp x, pp y, pp c ]
    SadcOverflows x y c -> sexprA "sadc_overflows" [ pp x, pp y, pp c ]
    UsbbOverflows x y c -> sexprA "usbb_overflows" [ pp x, pp y, pp c ]
    SsbbOverflows x y c -> sexprA "ssbb_overflows" [ pp x, pp y, pp c ]
    Bsf _ x -> sexprA "bsf" [ pp x ]
    Bsr _ x -> sexprA "bsr" [ pp x ]

ppApp :: (forall u . f u -> Doc)
      -> App f tp
      -> Doc
ppApp pp a0 = runIdentity $ ppAppA (Identity . pp) a0

------------------------------------------------------------------------
-- appType

instance HasRepr (App f) TypeRepr where
  typeRepr a =
    case a of
      Eq _ _       -> knownRepr
      Mux tp _ _ _ -> tp
      TupleField f _ i -> f P.!! i

      Trunc _ w -> BVTypeRepr w
      SExt  _ w -> BVTypeRepr w
      UExt  _ w -> BVTypeRepr w

      AndApp{} -> knownRepr
      OrApp{}  -> knownRepr
      NotApp{} -> knownRepr
      XorApp{} -> knownRepr

      BVAdd w _ _   -> BVTypeRepr w
      BVAdc w _ _ _ -> BVTypeRepr w
      BVSub w _ _   -> BVTypeRepr w
      BVSbb w _ _ _ -> BVTypeRepr w
      BVMul w _ _ -> BVTypeRepr w

      BVUnsignedLt{} -> knownRepr
      BVUnsignedLe{} -> knownRepr
      BVSignedLt{} -> knownRepr
      BVSignedLe{} -> knownRepr
      BVTestBit{} -> knownRepr

      BVComplement w _ -> BVTypeRepr w
      BVAnd w _ _ -> BVTypeRepr w
      BVOr  w _ _ -> BVTypeRepr w
      BVXor w _ _ -> BVTypeRepr w
      BVShl w _ _ -> BVTypeRepr w
      BVShr w _ _ -> BVTypeRepr w
      BVSar w _ _ -> BVTypeRepr w

      UadcOverflows{} -> knownRepr
      SadcOverflows{} -> knownRepr
      UsbbOverflows{} -> knownRepr
      SsbbOverflows{} -> knownRepr

      PopCount w _ -> BVTypeRepr w
      ReverseBytes w _ ->
        case leqMulCongr (LeqProof :: LeqProof 1 8) (leqProof (knownNat :: NatRepr 1) w) of
          LeqProof -> BVTypeRepr (natMultiply (knownNat :: NatRepr 8) w)
      Bsf w _ -> BVTypeRepr w
      Bsr w _ -> BVTypeRepr w
