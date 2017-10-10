{-|
Copyright        : (c) Galois, Inc 2015-2017
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
  ( -- * Constructor
    App(..)
    -- * Folding
  , ppApp
  , ppAppA
    -- * Utilities
  , ppNat
  , sexpr
  , sexprA
  ) where

import           Control.Monad.Identity
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Data.Macaw.Types

-----------------------------------------------------------------------
-- App

-- | App defines builtin operations on values.
data App (f :: Type -> *) (tp :: Type) where

  -- Compare for equality.
  Eq :: !(f tp) -> !(f tp) -> App f BoolType

  Mux :: !(TypeRepr tp) -> !(f BoolType) -> !(f tp) -> !(f tp) -> App f tp

  ----------------------------------------------------------------------
  -- Operations related to concatenating and extending bitvectors.

  -- Truncate a bitvector value.
  Trunc :: (1 <= n, n+1 <= m) => !(f (BVType m)) -> !(NatRepr n) -> App f (BVType n)
  -- Signed extension.
  SExt :: (1 <= m, m+1 <= n, 1 <= n) => f (BVType m) -> NatRepr n -> App f (BVType n)
  -- Unsigned extension.
  UExt :: (1 <= m, m+1 <= n, 1 <= n) => f (BVType m) -> NatRepr n -> App f (BVType n)

  ----------------------------------------------------------------------
  -- Boolean operations

  AndApp :: !(f BoolType) -> !(f BoolType) -> App f BoolType
  OrApp  :: !(f BoolType) -> !(f BoolType) -> App f BoolType
  NotApp :: !(f BoolType) -> App f BoolType
  XorApp  :: !(f BoolType) -> !(f BoolType) -> App f BoolType

  ----------------------------------------------------------------------
  -- Bitvector operations

  BVAdd :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)
  BVSub :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)

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

  -- Add two values and a carry bit to determine if they have an unsigned overflow.
  --
  -- This is the sum of three three values cannot be represented as an unsigned number.
  UadcOverflows :: (1 <= n)
                => !(NatRepr n)
                -> !(f (BVType n))
                -> !(f (BVType n))
                -> !(f BoolType)
                -> App f BoolType
  -- Add two values and a carry bit to determine if they have a signed
  -- overflow.
  SadcOverflows :: (1 <= n)
                => !(NatRepr n)
                -> !(f (BVType n))
                -> !(f (BVType n))
                -> !(f BoolType)
                -> App f BoolType

  -- Unsigned subtract with borrow overflow
  UsbbOverflows :: (1 <= n)
                => !(NatRepr n)
                -> !(f (BVType n))
                -> !(f (BVType n))
                -> !(f BoolType)
                -> App f BoolType

  -- Signed subtract with borrow overflow
  SsbbOverflows :: (1 <= n)
                => !(NatRepr n)
                -> !(f (BVType n))
                -> !(f (BVType n))
                -> !(f BoolType)
                -> App f BoolType

  -- | This returns the number of true bits in the input.
  PopCount :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> App f (BVType n)

  -- Return true if value contains even number of true bits.
  --EvenParity :: !(f (BVType 8)) -> App f BoolType

  -- Reverse the bytes in a bitvector expression.
  ReverseBytes :: (1 <= n) => !(NatRepr n) -> !(f (BVType (8*n))) -> App f (BVType (8*n))

  -- | bsf "bit scan forward" returns the index of the
  -- least-significant bit that is 1.  An equivalent way of stating
  -- this is that it returns the number "trailing" zero-bits.  This
  -- returns n if the value is zero.
  Bsf :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> App f (BVType n)

  -- | bsf "bit scan forward" returns the index of the
  -- most-significant bit that is 1.  An equivalent way of stating
  -- this is that it returns the number "least" zero-bits.  This
  -- returns n if the value is zero.
  Bsr :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> App f (BVType n)

  ----------------------------------------------------------------------
  -- Floating point operations

  -- | Return true if floating point value is a "quiet" NaN.
  FPIsQNaN :: !(FloatInfoRepr flt)
           -> !(f (FloatType flt))
           -> App f BoolType

  -- | Return true if floating point value is a "signaling" NaN.
  FPIsSNaN :: !(FloatInfoRepr flt)
           -> !(f (FloatType flt))
           -> App f BoolType

  FPAdd :: !(FloatInfoRepr flt)
        -> !(f (FloatType flt))
        -> !(f (FloatType flt))
        -> App f (FloatType flt)

  FPAddRoundedUp :: !(FloatInfoRepr flt)
                 -> !(f (FloatType flt))
                 -> !(f (FloatType flt))
                 -> App f BoolType

  FPSub :: !(FloatInfoRepr flt)
        -> !(f (FloatType flt))
        -> !(f (FloatType flt))
        -> App f (FloatType flt)

  FPSubRoundedUp
    :: !(FloatInfoRepr flt)
    -> !(f (FloatType flt))
    -> !(f (FloatType flt))
    -> App f BoolType

  FPMul :: !(FloatInfoRepr flt)
        -> !(f (FloatType flt))
        -> !(f (FloatType flt))
        -> App f (FloatType flt)

  FPMulRoundedUp :: !(FloatInfoRepr flt)
                 -> !(f (FloatType flt))
                 -> !(f (FloatType flt))
                 -> App f BoolType

  -- Divides two floating point numbers.
  FPDiv :: !(FloatInfoRepr flt)
        -> !(f (FloatType flt))
        -> !(f (FloatType flt))
        -> App f (FloatType flt)

  -- Compare if one floating is strictly less than another.
  FPLt :: !(FloatInfoRepr flt)
       -> !(f (FloatType flt))
       -> !(f (FloatType flt))
       -> App f BoolType

  -- Floating point equality (equates -0 and 0)
  FPEq :: !(FloatInfoRepr flt)
       -> !(f (FloatType flt))
       -> !(f (FloatType flt))
       -> App f BoolType

  -- | Convert a float from input type @flt@ to output type @flt'@
  FPCvt :: !(FloatInfoRepr flt)
        -> !(f (FloatType flt))
        -> !(FloatInfoRepr flt')
        -> App f (FloatType flt')

  FPCvtRoundsUp :: !(FloatInfoRepr flt)
                -> !(f (FloatType flt))
                -> !(FloatInfoRepr flt')
                -> App f BoolType

  FPFromBV :: !(f (BVType n))
           -> !(FloatInfoRepr flt)
           -> App f (FloatType flt)

  -- Convert a floating point value to a signed integer.
  -- If the conversion is inexact, then the value is truncated to zero.
  -- If the conversion is out of the range of the bitvector, then a floating
  -- point exception should be raised.
  -- If that exception is masked, then this returns -1 (as a signed bitvector).
  TruncFPToSignedBV :: (1 <= n)
                    => FloatInfoRepr flt
                    -> f (FloatType flt)
                    -> NatRepr n
                    -> App f (BVType n)

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
                   ]
                  )

instance OrdF f => OrdF (App f) where
  compareF = $(structuralTypeOrd [t|App|]
                   [ (DataArg 0                  `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|NatRepr|]       `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|FloatInfoRepr|] `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|TypeRepr|]      `TypeApp` AnyType, [|compareF|])
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

sexpr :: String -> [Doc] -> Doc
sexpr nm d = parens (hsep (text nm : d))

sexprA :: Applicative m => String -> [m Doc] -> m Doc
sexprA nm d = sexpr nm <$> sequenceA d

ppNat :: Applicative m => NatRepr n -> m Doc
ppNat n = pure (text (show n))

prettyPure :: (Applicative m, Pretty v) => v -> m Doc
prettyPure = pure . pretty

ppApp :: (forall u . f u -> Doc)
      -> App f tp
      -> Doc
ppApp pp a0 = runIdentity $ ppAppA (Identity . pp) a0

ppAppA :: Applicative m
      => (forall u . f u -> m Doc)
      -> App f tp
      -> m Doc
ppAppA pp a0 =
  case a0 of
    Mux _ c x y -> sexprA "mux" [ pp c, pp x, pp y ]
    Trunc x w -> sexprA "trunc" [ pp x, ppNat w ]
    SExt x w -> sexprA "sext" [ pp x, ppNat w ]
    UExt x w -> sexprA "uext" [ pp x, ppNat w ]
    AndApp x y -> sexprA "and" [ pp x, pp y ]
    OrApp  x y -> sexprA "or"  [ pp x, pp y ]
    NotApp x   -> sexprA "not" [ pp x ]
    XorApp  x y -> sexprA "xor"  [ pp x, pp y ]
    BVAdd _ x y -> sexprA "bv_add" [ pp x, pp y ]
    BVSub _ x y -> sexprA "bv_sub" [ pp x, pp y ]
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
    UadcOverflows _ x y c -> sexprA "uadc_overflows" [ pp x, pp y, pp c ]
    SadcOverflows _ x y c -> sexprA "sadc_overflows" [ pp x, pp y, pp c ]
    UsbbOverflows _ x y c -> sexprA "usbb_overflows" [ pp x, pp y, pp c ]
    SsbbOverflows _ x y c -> sexprA "ssbb_overflows" [ pp x, pp y, pp c ]
    Bsf _ x -> sexprA "bsf" [ pp x ]
    Bsr _ x -> sexprA "bsr" [ pp x ]

    -- Floating point
    FPIsQNaN rep x          -> sexprA "fpIsQNaN" [ prettyPure rep, pp x ]
    FPIsSNaN rep x          -> sexprA "fpIsSNaN" [ prettyPure rep, pp x ]
    FPAdd rep x y           -> sexprA "fpAdd" [ prettyPure rep, pp x, pp y ]
    FPAddRoundedUp rep x y  -> sexprA "fpAddRoundedUp" [ prettyPure rep, pp x, pp y ]
    FPSub rep x y           -> sexprA "fpSub" [ prettyPure rep, pp x, pp y ]
    FPSubRoundedUp rep x y  -> sexprA "fpSubRoundedUp" [ prettyPure rep, pp x, pp y ]
    FPMul rep x y           -> sexprA "fpMul" [ prettyPure rep, pp x, pp y ]
    FPMulRoundedUp rep x y  -> sexprA "fpMulRoundedUp" [ prettyPure rep, pp x, pp y ]
    FPDiv rep x y           -> sexprA "fpDiv" [ prettyPure rep, pp x, pp y ]
    FPLt rep x y            -> sexprA "fpLt" [ prettyPure rep, pp x, pp y ]
    FPEq rep x y            -> sexprA "fpEq" [ prettyPure rep, pp x, pp y ]
    FPCvt src x tgt         -> sexprA "fpCvt" [ prettyPure src, pp x, prettyPure tgt ]
    FPCvtRoundsUp src x tgt -> sexprA "fpCvtRoundsUp" [ prettyPure src, pp x, prettyPure tgt ]
    FPFromBV x tgt          -> sexprA "fpFromBV" [ pp x, prettyPure tgt ]
    TruncFPToSignedBV _ x w -> sexprA "truncFP_sbv" [ pp x, ppNat w]

------------------------------------------------------------------------
-- appType

instance HasRepr (App f) TypeRepr where
  typeRepr a =
   case a of
    Mux tp _ _ _ -> tp
    Trunc _ w -> BVTypeRepr w
    SExt  _ w -> BVTypeRepr w
    UExt  _ w -> BVTypeRepr w

    AndApp{} -> knownType
    OrApp{}  -> knownType
    NotApp{} -> knownType
    XorApp{} -> knownType

    BVAdd w _ _ -> BVTypeRepr w
    BVSub w _ _ -> BVTypeRepr w
    BVMul w _ _ -> BVTypeRepr w

    BVUnsignedLt{} -> knownType
    BVUnsignedLe{} -> knownType
    BVSignedLt{} -> knownType
    BVSignedLe{} -> knownType
    BVTestBit{} -> knownType

    BVComplement w _ -> BVTypeRepr w
    BVAnd w _ _ -> BVTypeRepr w
    BVOr  w _ _ -> BVTypeRepr w
    BVXor w _ _ -> BVTypeRepr w
    BVShl w _ _ -> BVTypeRepr w
    BVShr w _ _ -> BVTypeRepr w
    BVSar w _ _ -> BVTypeRepr w
    Eq _ _       -> knownType


    UadcOverflows{} -> knownType
    SadcOverflows{} -> knownType
    UsbbOverflows{} -> knownType
    SsbbOverflows{} -> knownType

    PopCount w _ -> BVTypeRepr w
    ReverseBytes w _ ->
      case leqMulCongr (LeqProof :: LeqProof 1 8) (leqProof (knownNat :: NatRepr 1) w) of
        LeqProof -> BVTypeRepr (natMultiply (knownNat :: NatRepr 8) w)
    Bsf w _ -> BVTypeRepr w
    Bsr w _ -> BVTypeRepr w

    -- Floating point
    FPIsQNaN _ _ -> knownType
    FPIsSNaN _ _ -> knownType
    FPAdd rep _ _ -> floatTypeRepr rep
    FPAddRoundedUp{} -> knownType
    FPSub rep _ _ -> floatTypeRepr rep
    FPSubRoundedUp{} -> knownType
    FPMul rep _ _ -> floatTypeRepr rep
    FPMulRoundedUp{} -> knownType
    FPDiv rep _ _ -> floatTypeRepr rep
    FPLt{} -> knownType
    FPEq{} -> knownType
    FPCvt _ _ tgt   -> floatTypeRepr tgt
    FPCvtRoundsUp{} -> knownType
    FPFromBV _ tgt  -> floatTypeRepr tgt
    TruncFPToSignedBV _ _ w -> BVTypeRepr w
