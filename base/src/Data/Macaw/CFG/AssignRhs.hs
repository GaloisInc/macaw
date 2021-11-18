{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.CFG.AssignRhs
  ( AssignRhs(..)
    -- * MemRepr
  , MemRepr(..)
  , memReprBytes
    -- * Architecture type families
  , RegAddrWidth
  , ArchReg
  , ArchFn
  , ArchStmt
  , ArchTermStmt
    -- * Synonyms
  , RegAddrWord
  , ArchAddrWidth
  , ArchAddrWord
  , ArchMemAddr
  ) where

import qualified Data.Kind as Kind
import           Data.Macaw.CFG.App
import           Data.Macaw.Memory (Endianness(..), MemWord, MemAddr)
import           Data.Macaw.Types
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC (FoldableFC(..))
import           Data.Proxy
import           Numeric.Natural
import           Prettyprinter

-- | Width of register used to store addresses.
type family RegAddrWidth (r :: Type -> Kind.Type) :: Nat

-- | A word for the given architecture register type.
type RegAddrWord r = MemWord (RegAddrWidth r)

-- | Type family for defining what a "register" is for this architecture.
--
-- Registers include things like the general purpose registers, any flag
-- registers that can be read and written without side effects,
type family ArchReg (arch :: Kind.Type) = (reg :: Type -> Kind.Type) | reg -> arch
  -- Note the injectivity constraint. This makes GHC quit bothering us
  -- about ambigous types for functions taking ArchRegs as arguments.

-- | A type family for architecture specific functions.
--
-- The functions associated with architecture-function depend on the
-- contents of memory and implicit components of the processor state,
-- but they should not affect any of the architecture
-- registers in @ArchReg arch@.
--
-- Architecture specific functions are required to implement
-- `FoldableFC`, and the evaluation of an architecture specific
-- function may only depend on the value stored in a general purpose
-- register if it is given through the @fn@ parameter and provided
-- when folding over values.  This is required for accurate def-use
-- analysis of general purpose registers.
type family ArchFn (arch :: Kind.Type) = (fn :: (Type -> Kind.Type) -> Type -> Kind.Type) | fn -> arch

-- | A type family for defining architecture-specific statements.
--
-- The second parameter is used to denote the underlying values in the
-- statements so that we can use ArchStmts with multiple CFGs.
type family ArchStmt (arch :: Kind.Type) = (stmt :: (Type -> Kind.Type) -> Kind.Type) | stmt -> arch

-- | A type family for defining architecture-specific statements that
-- may have instruction-specific effects on control-flow and register state.
--
-- An architecture-specific terminal statement may have side effects and change register
-- values, it may or may not return to the current function.
type family ArchTermStmt (arch :: Kind.Type) :: (Type -> Kind.Type) -> Kind.Type
   -- NOTE: Not injective because PPC32 and PPC64 use the same type.

-- | Number of bits in addreses for architecture.
type ArchAddrWidth arch = RegAddrWidth (ArchReg arch)

-- | A word for the given architecture bitwidth.
type ArchAddrWord arch = RegAddrWord (ArchReg arch)

-- | An address for a given architecture.
type ArchMemAddr arch = MemAddr (ArchAddrWidth arch)

------------------------------------------------------------------------
-- MemRepr

-- | The provides information sufficient to read supported types of values from
-- memory such as the number of bytes and endianness.
data MemRepr (tp :: Type) where
  -- | Denotes a bitvector with the given number of bytes and endianness.
  BVMemRepr :: (1 <= w) => !(NatRepr w) -> !Endianness -> MemRepr (BVType (8*w))
  -- | A floating point value (stored in given endianness.
  FloatMemRepr :: !(FloatInfoRepr f) -> !Endianness -> MemRepr (FloatType f)
  -- | A vector of values with zero entry first.
  --
  -- The first value is stored at the address, the second is stored at
  -- address + sizeof eltType, etc.
  PackedVecMemRepr :: !(NatRepr n) -> !(MemRepr tp) -> MemRepr (VecType n tp)

ppEndianness :: Endianness -> Doc ann
ppEndianness LittleEndian = "le"
ppEndianness BigEndian    = "be"

instance Pretty (MemRepr tp) where
  pretty (BVMemRepr w end) = "bv" <> ppEndianness end <> viaShow w
  pretty (FloatMemRepr f end) = pretty f <> ppEndianness end
  pretty (PackedVecMemRepr w r) = "v" <> viaShow w <> pretty r

instance Show (MemRepr tp) where
  show = show . pretty

-- | Return the number of bytes this uses in memory.
memReprBytes :: MemRepr tp -> Natural
memReprBytes (BVMemRepr x _) = natValue x
memReprBytes (FloatMemRepr f _) = natValue (floatInfoBytes f)
memReprBytes (PackedVecMemRepr w r) = natValue w * memReprBytes r

instance TestEquality MemRepr where
  testEquality (BVMemRepr xw xe) (BVMemRepr yw ye) = do
    Refl <- testEquality xw yw
    if xe == ye then Just Refl else Nothing
  testEquality (FloatMemRepr xf xe) (FloatMemRepr yf ye) = do
    Refl <- testEquality xf yf
    if xe == ye then Just Refl else Nothing
  testEquality (PackedVecMemRepr xn xe) (PackedVecMemRepr yn ye) = do
    Refl <- testEquality xn yn
    Refl <- testEquality xe ye
    Just Refl
  testEquality _ _ = Nothing

instance Hashable (MemRepr tp) where
  hashWithSalt s mr =
    case mr of
      BVMemRepr w e        -> s `hashWithSalt` (0::Int) `hashWithSalt` w `hashWithSalt` e
      FloatMemRepr r e     -> s `hashWithSalt` (1::Int) `hashWithSalt` r `hashWithSalt` e
      PackedVecMemRepr n e -> s `hashWithSalt` (2::Int) `hashWithSalt` n `hashWithSalt` e

instance HashableF MemRepr where
  hashWithSaltF = hashWithSalt

instance OrdF MemRepr where
  compareF (BVMemRepr xw xe) (BVMemRepr yw ye) =
    joinOrderingF (compareF xw yw) $
     fromOrdering (compare  xe ye)
  compareF BVMemRepr{} _ = LTF
  compareF _ BVMemRepr{} = GTF
  compareF (FloatMemRepr xf xe) (FloatMemRepr yf ye) =
    joinOrderingF (compareF xf yf) $
    fromOrdering (compare  xe ye)
  compareF FloatMemRepr{} _ = LTF
  compareF _ FloatMemRepr{} = GTF
  compareF (PackedVecMemRepr xn xe) (PackedVecMemRepr yn ye) =
    joinOrderingF (compareF xn yn) $
    joinOrderingF (compareF  xe ye) $
    EQF

instance HasRepr MemRepr TypeRepr where
  typeRepr (BVMemRepr w _) =
    let r = (natMultiply n8 w)
     in case leqMulPos (Proxy :: Proxy 8) w of
          LeqProof -> BVTypeRepr r
  typeRepr (FloatMemRepr f _) = FloatTypeRepr f
  typeRepr (PackedVecMemRepr n e) = VecTypeRepr n (typeRepr e)

------------------------------------------------------------------------
-- AssignRhs

-- | The right hand side of an assignment is an expression that
-- returns a value.
data AssignRhs (arch :: Kind.Type) (f :: Type -> Kind.Type) tp where
  -- | An expression that is computed from evaluating subexpressions.
  EvalApp :: !(App f tp)
          -> AssignRhs arch f tp

  -- | An expression with an undefined value.
  SetUndefined :: !(TypeRepr tp)
               -> AssignRhs arch f tp

  -- | Read memory at given location.
  ReadMem :: !(f (BVType (ArchAddrWidth arch)))
          -> !(MemRepr tp)
          -> AssignRhs arch f tp

  -- | @CondReadMem tp cond addr v@ reads from memory at the given address if the
  -- condition is true and returns the value if it false.
  CondReadMem :: !(MemRepr tp)
              -> !(f BoolType)
              -> !(f (BVType (ArchAddrWidth arch)))
              -> !(f tp)
              -> AssignRhs arch f tp

  -- Call an architecture specific function that returns some result.
  EvalArchFn :: !(ArchFn arch f tp)
             -> !(TypeRepr tp)
             -> AssignRhs arch f tp

instance HasRepr (AssignRhs arch f) TypeRepr where
  typeRepr rhs =
    case rhs of
      EvalApp a -> typeRepr a
      SetUndefined tp -> tp
      ReadMem _ tp -> typeRepr tp
      CondReadMem tp _ _ _ -> typeRepr tp
      EvalArchFn _ rtp -> rtp

instance FoldableFC (ArchFn arch) => FoldableFC (AssignRhs arch) where
  foldMapFC go v =
    case v of
      EvalApp a -> foldMapFC go a
      SetUndefined _w -> mempty
      ReadMem addr _ -> go addr
      CondReadMem _ c a d -> go c <> go a <> go d
      EvalArchFn f _ -> foldMapFC go f
