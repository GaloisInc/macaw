{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
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
  , ArchSegmentOff
  , ArchMemAddr
  ) where

import Data.Macaw.CFG.App
import Data.Macaw.Memory (Endianness(..), MemSegmentOff, MemWord, MemAddr)
import Data.Macaw.Types

import Data.Monoid
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Parameterized.TraversableFC (FoldableFC(..))
import Data.Proxy
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

-- | Width of register used to store addresses.
type family RegAddrWidth (r :: Type -> *) :: Nat

-- | A word for the given architecture register type.
type RegAddrWord r = MemWord (RegAddrWidth r)

-- | Type family for defining what a "register" is for this architecture.
--
-- Registers include things like the general purpose registers, any flag
-- registers that can be read and written without side effects,
type family ArchReg (arch :: *) = (reg :: Type -> *) | reg -> arch
  -- Note the injectivity constraint. This makes GHC quit bothering us
  -- about ambigous types for functions taking ArchRegs as arguments.

-- | A type family for architecture specific functions.
--
-- These functions may return a value.  They may depend on the current state of
-- the heap, but should not affect the processor state.
--
-- The function may depend on the set of registers defined so far, and the type
-- of the result.
type family ArchFn (arch :: *) = (fn :: (Type -> *) -> Type -> *) | fn -> arch

-- | A type family for defining architecture-specific statements.
--
-- The second parameter is used to denote the underlying values in the
-- statements so that we can use ArchStmts with multiple CFGs.
type family ArchStmt (arch :: *) = (stmt :: (Type -> *) -> *) | stmt -> arch

-- | A type family for defining architecture-specific statements that
-- may have instruction-specific effects on control-flow and register state.
--
-- The second type parameter is the ids phantom type used to provide
-- uniqueness of Nonce values that identify assignments.
--
-- An architecture-specific terminal statement may have side effects and change register
-- values, it may or may not return to the current function.  If it does return to the
-- current function, it is assumed to be at most one location, and the block-translator
-- must provide that value at translation time.
type family ArchTermStmt (arch :: *) :: * -> *
   -- NOTE: Not injective because PPC32 and PPC64 use the same type.

-- | Number of bits in addreses for architecture.
type ArchAddrWidth arch = RegAddrWidth (ArchReg arch)

-- | A pair containing a segment and valid offset within the segment.
type ArchSegmentOff arch = MemSegmentOff (ArchAddrWidth arch)

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

instance Pretty (MemRepr tp) where
  pretty (BVMemRepr w BigEndian)    = text "bvbe" <+> text (show w)
  pretty (BVMemRepr w LittleEndian) = text "bvle" <+> text (show w)

instance Show (MemRepr tp) where
  show = show . pretty

-- | Return the number of bytes this uses in memory.
memReprBytes :: MemRepr tp -> Integer
memReprBytes (BVMemRepr x _) = natValue x

instance TestEquality MemRepr where
  testEquality (BVMemRepr xw xe) (BVMemRepr yw ye) =
    if xe == ye then do
      Refl <- testEquality xw yw
      Just Refl
     else
      Nothing

instance OrdF MemRepr where
  compareF (BVMemRepr xw xe) (BVMemRepr yw ye) =
    joinOrderingF (compareF xw yw) $
     fromOrdering (compare  xe ye)

instance HasRepr MemRepr TypeRepr where
  typeRepr (BVMemRepr w _) =
    let r = (natMultiply n8 w)
     in case leqMulPos (Proxy :: Proxy 8) w of
          LeqProof -> BVTypeRepr r

------------------------------------------------------------------------
-- AssignRhs

-- | The right hand side of an assignment is an expression that
-- returns a value.
data AssignRhs (arch :: *) (f :: Type -> *) tp where
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
