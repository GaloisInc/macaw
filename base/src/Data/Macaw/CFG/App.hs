{-|
This defines a data type `App` for representing operations that can be
applied to a range of values.  We call it an `App` because it
represents an application of an operation.  In mathematics, we would
probably call it a signature.
-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.CFG.App
  ( -- * App
    App(..)
  , ppApp
  , ppAppA
    -- ** Rendering
  , AppRender(..)
  , AppRenderArg(..)
  , rendApp
    -- * Casting proof objects.
  , WidthEqProof(..)
  , widthEqProofEq
  , widthEqProofCompare
  , widthEqSource
  , widthEqTarget
  , widthEqSym
  ) where

import           Control.Monad.Identity
import qualified Data.Kind as Kind
import           Data.Parameterized.Classes
import qualified Data.Parameterized.List as P
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TH.GADT
import Data.Parameterized.TraversableFC
    ( TraversableFC(..),
      FoldableFC(toListFC, foldMapFC, foldlFC'),
      FunctorFC(..),
      fmapFCDefault,
      foldMapFCDefault )
import           Data.Text (Text)
import qualified Data.Text as Text
import Numeric.Natural ( Natural )
import           Prettyprinter

import           Data.Macaw.Types
import           Data.Macaw.Utils.Pretty

-----------------------------------------------------------------------
-- App

-- | Data type to represent that two types use the same number of
-- bits, and thus can be bitcast.
--
-- Note. This datatype needs to balance several competing
-- requirements.  It needs to support all bitcasts needed by
-- architectures, represent bitcasts compactly, allow bitcasts to be
-- removed during optimization, and allow bitcasts to be symbolically
-- simulated.
--
-- Due to these requirements, we have a fairly limited set of proof
-- rules.  New rules can be added, but need to be balanced against the
-- above set of goals.  By design we do not have transitivity or
-- equality, as those can be obtained by respectively chaining
-- bitcasts or eliminating them.
data WidthEqProof (in_tp :: Type) (out_tp :: Type) where
  PackBits :: (1 <= n, 2 <= n, 1 <= w)
           => !(NatRepr n)
           -> !(NatRepr w)
           -> WidthEqProof (VecType n (BVType w)) (BVType (n * w))
  UnpackBits :: (1 <= n, 2 <= n, 1 <= w)
             => !(NatRepr n)
             -> !(NatRepr w)
             -> WidthEqProof (BVType (n * w)) (VecType n (BVType w))
  FromFloat :: !(FloatInfoRepr ftp)
            -> WidthEqProof (FloatType ftp) (BVType (FloatInfoBits ftp))
  ToFloat :: !(FloatInfoRepr ftp)
          -> WidthEqProof (BVType (FloatInfoBits ftp)) (FloatType ftp)

  -- | Convert between vector types that are equivalent.
  VecEqCongruence :: !(NatRepr n)
                  -> !(WidthEqProof i o)
                  -> WidthEqProof (VecType n i) (VecType n o)

  -- | Type is equal to itself.
  WidthEqRefl  :: !(TypeRepr tp) -> WidthEqProof tp tp

  -- | Allows transitivity composing proofs.
  WidthEqTrans :: !(WidthEqProof x y) -> !(WidthEqProof y z) -> WidthEqProof x z

-- | Apply symmetry to a width equality proof.
widthEqSym :: WidthEqProof x y -> WidthEqProof y x
widthEqSym (PackBits n w) = UnpackBits n w
widthEqSym (UnpackBits n w) = PackBits n w
widthEqSym (FromFloat r) = ToFloat r
widthEqSym (ToFloat r) = FromFloat r
widthEqSym (VecEqCongruence n p) = VecEqCongruence n (widthEqSym p)
widthEqSym (WidthEqRefl tp) = WidthEqRefl tp
widthEqSym (WidthEqTrans x y) = WidthEqTrans (widthEqSym y) (widthEqSym x)

-- | Return the input type of the width equality proof
widthEqSource :: WidthEqProof i o -> TypeRepr i
widthEqSource (PackBits n w) = VecTypeRepr n (BVTypeRepr w)
widthEqSource (UnpackBits n w) =
  case leqMulPos n w of
    LeqProof -> BVTypeRepr (natMultiply n w)
widthEqSource (FromFloat f) = FloatTypeRepr f
widthEqSource (ToFloat f) =
  case floatInfoBitsIsPos f of
    LeqProof -> BVTypeRepr (floatInfoBits f)
widthEqSource (VecEqCongruence n r) = VecTypeRepr n (widthEqSource r)
widthEqSource (WidthEqRefl x) = x
widthEqSource (WidthEqTrans x _) = widthEqSource x

-- | Return the result type of the width equality proof
widthEqTarget :: WidthEqProof i o -> TypeRepr o
widthEqTarget (PackBits n w) =
  case leqMulPos n w of
    LeqProof -> BVTypeRepr (natMultiply n w)
widthEqTarget (UnpackBits n w) = VecTypeRepr n (BVTypeRepr w)
widthEqTarget (FromFloat f) =
  case floatInfoBitsIsPos f of
    LeqProof -> BVTypeRepr (floatInfoBits f)
widthEqTarget (ToFloat f) = FloatTypeRepr f
widthEqTarget (VecEqCongruence n r) = VecTypeRepr n (widthEqTarget r)
widthEqTarget (WidthEqRefl x) = x
widthEqTarget (WidthEqTrans _ y) = widthEqTarget y

-- Force app to be in template-haskell context.
$(pure [])

-- | Compare two proofs, and return truei if the input/output types
-- are the same.
widthEqProofEq :: WidthEqProof xi xo
               -> WidthEqProof yi yo
               -> Maybe (WidthEqProof xi xo :~: WidthEqProof yi yo)
widthEqProofEq p q = do
  Refl <- testEquality (widthEqSource p) (widthEqSource q)
  Refl <- testEquality (widthEqTarget p) (widthEqTarget q)
  pure Refl

-- | Compare proofs based on ordering of source and target.
widthEqProofCompare :: WidthEqProof xi xo
                    -> WidthEqProof yi yo
                    -> OrderingF (WidthEqProof xi xo) (WidthEqProof yi yo)
widthEqProofCompare p q =
  joinOrderingF (compareF (widthEqSource p) (widthEqSource q)) $
    joinOrderingF (compareF (widthEqTarget p) (widthEqTarget q)) $
      EQF

-- | This datatype defines operations used on multiple architectures.
--
-- These operations are all total functions.  Different architecture tend to have
-- different ways of raising signals or exceptions, and so partial functions are
-- all architecture specific.
data App (f :: Type -> Kind.Type) (tp :: Type) where

  -- | Compare for equality.
  Eq :: !(f tp) -> !(f tp) -> App f BoolType

  Mux :: !(TypeRepr tp) -> !(f BoolType) -> !(f tp) -> !(f tp) -> App f tp

  ----------------------------------------------------------------------
  -- Boolean operations

  AndApp :: !(f BoolType) -> !(f BoolType) -> App f BoolType
  OrApp  :: !(f BoolType) -> !(f BoolType) -> App f BoolType
  NotApp :: !(f BoolType) -> App f BoolType
  XorApp  :: !(f BoolType) -> !(f BoolType) -> App f BoolType

  ----------------------------------------------------------------------
  -- Tuples

  -- | Create a tuple from a list of fields
  MkTuple :: !(P.List TypeRepr flds)
          -> !(P.List f flds)
          -> App f (TupleType flds)

  -- | Extract the value out of a tuple.
  TupleField :: !(P.List TypeRepr l) -> !(f (TupleType l)) -> !(P.Index l r) -> App f r

  ----------------------------------------------------------------------
  -- Vector

  -- | Extracts an element at given constant index from vector
  ExtractElement :: !(TypeRepr tp) -> !(f (VecType n tp)) -> !Int -> App f tp

  -- | Sets an element at given constant in vector.
  InsertElement :: !(TypeRepr (VecType n tp))
                -> !(f (VecType n tp)) -> !Int -> !(f tp) -> App f (VecType n tp)

  ----------------------------------------------------------------------
  -- Operations related to concatenating and extending bitvectors.

  -- | Given a @m@-bit bitvector and a natural number @n@ less than @m@, this returns
  -- the bitvector with the @n@ least significant bits.
  Trunc :: (1 <= n, n+1 <= m)
        => !(f (BVType m)) -> !(NatRepr n) -> App f (BVType n)

  -- | Given a @m@-bit bitvector @x@ and a natural number @n@ greater
  -- than @m@, this returns the bitvector with the same @m@ least
  -- signficant bits, and where the new bits are the same as the most
  -- significant bit in @x@.
  SExt :: (1 <= m, m+1 <= n, 1 <= n)
       => !(f (BVType m)) -> !(NatRepr n) -> App f (BVType n)
  -- | Given a @m@-bit bitvector @x@ and a natural number @n@ greater
  -- than @m@, this returns the bitvector with the same @m@ least
  -- signficant bits, and where the new bits are all @false@.
  UExt :: (1 <= m, m+1 <= n, 1 <= n)
       => !(f (BVType m))
       -> !(NatRepr n)
       -> App f (BVType n)

  -- | This casts an expression from one type to another that should
  -- use the same number of bytes in memory.
  Bitcast :: !(f tp) -> !(WidthEqProof tp out) -> App f out

  ----------------------------------------------------------------------
  -- Bitvector operations

  -- | @BVAdd w x y@ denotes @x + y@.
  BVAdd :: (1 <= n)
        => !(NatRepr n)
        -> !(f (BVType n))
        -> !(f (BVType n))
        -> App f (BVType n)

  -- | @BVAdc w x y c@ denotes @x + y + (c ? 1 : 0)@.
  BVAdc :: (1 <= n)
        => !(NatRepr n)
        -> !(f (BVType n))
        -> !(f (BVType n))
        -> !(f BoolType)
        -> App f (BVType n)

  -- | @BVSub w x y@ denotes @x - y@.
  BVSub :: (1 <= n)
        => !(NatRepr n)
        -> !(f (BVType n))
        -> !(f (BVType n))
        -> App f (BVType n)

  -- | @BVSbb w x y b@ denotes @(x - y) - (b ? 1 : 0)@.
  BVSbb :: (1 <= n)
        => !(NatRepr n)
        -> !(f (BVType n))
        -> !(f (BVType n))
        -> !(f BoolType)
        -> App f (BVType n)

  -- Multiply two numbers
  BVMul :: (1 <= n)
        => !(NatRepr n)
        -> !(f (BVType n))
        -> !(f (BVType n))
        -> App f (BVType n)

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

  -- | Left shift (e.g. `BVShl x y` denotes `fromUnsigned (toUnsigned x * 2 ^ toUnsigned y)`
  BVShl :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)
  -- | Unsigned right shift (e.g. `BVShr x y` denotes `fromUnsigned (toUnsigned x / 2 ^ toUnsigned y)`
  BVShr :: (1 <= n) => !(NatRepr n) -> !(f (BVType n)) -> !(f (BVType n)) -> App f (BVType n)
  -- | Arithmetic right shift (e.g. `BVSar x y` denotes `fromUnsigned (toSigned x / 2 ^ toUnsigned y)`
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
                   , (ConType [t|WidthEqProof|] `TypeApp` AnyType `TypeApp` AnyType,
                      [|widthEqProofEq|])
                   ]
                  )

instance HashableF f => Hashable (App f tp) where
  hashWithSalt = $(structuralHashWithSalt [t|App|]
                     [ (DataArg 0 `TypeApp` AnyType, [|hashWithSaltF|])
                     , (ConType [t|TypeRepr|] `TypeApp` AnyType, [|\s _c -> s|])
                     , (ConType [t|P.List|] `TypeApp` ConType [t|TypeRepr|] `TypeApp` AnyType
                       , [|\s _c -> s|])
                     , (ConType [t|P.List|] `TypeApp` DataArg 0 `TypeApp` AnyType
                       , [|\s l -> foldlFC' hashWithSaltF s l |])
                     , (ConType [t|WidthEqProof|] `TypeApp` AnyType `TypeApp` AnyType
                       , [|\s _c -> s|])
                     ]
                  )

instance HashableF f => HashableF (App f) where
  hashWithSaltF = hashWithSalt

instance OrdF f => OrdF (App f) where
  compareF = $(structuralTypeOrd [t|App|]
                   [ (DataArg 0                  `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|NatRepr|]       `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|FloatInfoRepr|] `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|TypeRepr|]      `TypeApp` AnyType, [|compareF|])
                   , (ConType [t|P.List|] `TypeApp` ConType [t|TypeRepr|] `TypeApp` AnyType,
                      [|compareF|])
                  , (ConType [t|P.List|] `TypeApp` DataArg 0 `TypeApp` AnyType,
                      [|compareF|])
                   , (ConType [t|P.Index|] `TypeApp` AnyType `TypeApp` AnyType,
                      [|compareF|])
                   , (ConType [t|WidthEqProof|] `TypeApp` AnyType `TypeApp` AnyType,
                      [|widthEqProofCompare|])
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
  traverseFC =
    $(structuralTraversal [t|App|]
      [ (ConType [t|P.List|] `TypeApp` DataArg 0 `TypeApp` AnyType
        , [|traverseFC|]
        )
      ])

------------------------------------------------------------------------
-- App pretty printing

data AppRenderArg (f :: Type -> Kind.Type) where
  Val :: f tp -> AppRenderArg f
  -- Type argument (for bitcast)
  Type :: !(TypeRepr tp) -> AppRenderArg f
  -- Index into vector or tuple (must be valid for type)
  Index :: Natural -> AppRenderArg f
  -- Width argument passed to extension (must be positive)
  Width :: Natural -> AppRenderArg f

data AppRender (f :: Type -> Kind.Type) = AppRender Text [AppRenderArg f]

-- | Pretty print an 'App' as an expression using the given function
-- for printing arguments.
rendApp :: App f tp -> AppRender f
rendApp a0 = do
  let app = AppRender
  case a0 of
    Eq x y       -> app "eq" [ Val x, Val y ]
    Mux   _ c x y -> app "mux" [ Val c, Val x, Val y ]
    AndApp x y -> app "and" [ Val x, Val y ]
    OrApp  x y -> app "or"  [ Val x, Val y ]
    NotApp x   -> app "not" [ Val x ]
    XorApp  x y -> app "xor"  [ Val x, Val y ]
    MkTuple _ flds -> app "tuple" (toListFC Val flds)
    TupleField _ x i -> app "tuple_field" [ Val x, Index (fromInteger (P.indexValue i)) ]
    ExtractElement _ v i -> app "extract_element" [ Val v, Index (fromIntegral i) ]
    InsertElement _ s i v -> app "insert_element" [ Val s, Index (fromIntegral i), Val v ]
    Trunc x w -> app "trunc" [ Val x, Width (natValue w) ]
    SExt x w -> app "sext" [ Val x, Width (natValue w) ]
    UExt x w -> app "uext" [ Val x, Width (natValue w) ]
    Bitcast x tp -> app "bitcast" [ Val x, Type (widthEqTarget tp) ]
    BVAdd _ x y   -> app "bv_add" [ Val x, Val y ]
    BVAdc _ x y c -> app "bv_adc" [ Val x, Val y, Val c ]
    BVSub _ x y -> app "bv_sub" [ Val x, Val y ]
    BVSbb _ x y b -> app "bv_sbb" [ Val x, Val y, Val b ]
    BVMul _ x y -> app "bv_mul" [ Val x, Val y ]
    BVUnsignedLt x y  -> app "bv_ult"  [ Val x, Val y ]
    BVUnsignedLe x y  -> app "bv_ule"  [ Val x, Val y ]
    BVSignedLt x y    -> app "bv_slt"  [ Val x, Val y ]
    BVSignedLe x y    -> app "bv_sle"  [ Val x, Val y ]
    BVTestBit x i -> app "bv_testbit" [ Val x, Val i]
    BVComplement _ x -> app "bv_complement" [ Val x ]
    BVAnd _ x y -> app "bv_and" [ Val x, Val y ]
    BVOr  _ x y -> app "bv_or"  [ Val x, Val y ]
    BVXor _ x y -> app "bv_xor" [ Val x, Val y ]
    BVShl _ x y -> app "bv_shl" [ Val x, Val y ]
    BVShr _ x y -> app "bv_shr" [ Val x, Val y ]
    BVSar _ x y -> app "bv_sar" [ Val x, Val y ]
    PopCount _ x -> app "popcount" [ Val x ]
    ReverseBytes _ x -> app "reverse_bytes" [ Val x ]
    UadcOverflows x y c -> app "uadc_overflows" [ Val x, Val y, Val c ]
    SadcOverflows x y c -> app "sadc_overflows" [ Val x, Val y, Val c ]
    UsbbOverflows x y c -> app "usbb_overflows" [ Val x, Val y, Val c ]
    SsbbOverflows x y c -> app "ssbb_overflows" [ Val x, Val y, Val c ]
    Bsf _ x -> app "bsf" [ Val x ]
    Bsr _ x -> app "bsr" [ Val x ]

-- | Pretty print an 'App' as an expression using the given function
-- for printing arguments.
ppAppA :: forall m f tp ann
       . Applicative m
       => (forall u . f u -> m (Doc ann))
       -> App f tp
       -> m (Doc ann)
ppAppA pp a0 =
  case rendApp a0 of
    AppRender nm args -> do
      let rendArg :: AppRenderArg f -> m (Doc ann)
          rendArg (Val v) = pp v
          rendArg (Type tp) = pure (viaShow tp)
          rendArg (Index i) = pure (viaShow i)
          rendArg (Width i) = pure (viaShow i)
      sexpr (Text.unpack nm) <$> traverse rendArg args

ppApp :: (forall u . f u -> Doc ann)
      -> App f tp
      -> Doc ann
ppApp pp a0 = runIdentity $ ppAppA (Identity . pp) a0

------------------------------------------------------------------------
-- appType

instance HasRepr (App f) TypeRepr where
  typeRepr a =
    case a of
      Eq _ _       -> knownRepr
      Mux tp _ _ _ -> tp

      AndApp{} -> knownRepr
      OrApp{}  -> knownRepr
      NotApp{} -> knownRepr
      XorApp{} -> knownRepr

      MkTuple fieldTypes _ -> TupleTypeRepr fieldTypes
      TupleField f _ i -> f P.!! i

      ExtractElement tp _ _ -> tp
      InsertElement tp _ _ _ -> tp

      Trunc _ w -> BVTypeRepr w
      SExt  _ w -> BVTypeRepr w
      UExt  _ w -> BVTypeRepr w
      Bitcast _ p -> widthEqTarget p

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
