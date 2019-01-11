{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines the monad used to map Reopt blocks to Crucible.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wwarn #-}
module Data.Macaw.Symbolic.PersistentState
  ( -- * CrucPersistentState
    CrucPersistentState(..)
  , initCrucPersistentState
    -- * Types
  , ToCrucibleType
  , ToCrucibleFloatInfo
  , FromCrucibleFloatInfo
  , CtxToCrucibleType
  , ArchRegContext
  , typeToCrucible
  , floatInfoToCrucible
  , floatInfoFromCrucible
  , typeCtxToCrucible
  , typeListToCrucible
  , macawAssignToCrucM
  , memReprToCrucible
    -- * Register index map
  , RegIndexMap
  , mkRegIndexMap
  , IndexPair(..)
    -- * Values
  , MacawCrucibleValue(..)
  ) where


import           Control.Monad.ST (ST)
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Types as M
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import qualified Data.Parameterized.List as P
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce (NonceGenerator)
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.LLVM.MemModel as MM

------------------------------------------------------------------------
-- Type mappings

type family ToCrucibleTypeList (l :: [M.Type]) :: Ctx C.CrucibleType where
  ToCrucibleTypeList '[]      = EmptyCtx
  ToCrucibleTypeList (h ': l) = ToCrucibleTypeList l ::> ToCrucibleType h

-- | A type family that converts Macaw types ('M.Type') into Crucible types
-- ('C.CrucibleType')
--
-- Most values are of type 'M.BVType' (bitvectors) - these are represented in
-- Crucible as 'MM.LLVMPointerType', which are special bitvectors that can also
-- be pointers in the LLVM memory model.
type family ToCrucibleType (tp :: M.Type) :: C.CrucibleType where
  ToCrucibleType (M.BVType w)     = MM.LLVMPointerType w
  ToCrucibleType (M.FloatType fi) = C.FloatType (ToCrucibleFloatInfo fi)
  ToCrucibleType ('M.TupleType l) = C.StructType (ToCrucibleTypeList l)
  ToCrucibleType M.BoolType       = C.BaseToType C.BaseBoolType

-- | Convert Macaw float types into Crucible float types
type family ToCrucibleFloatInfo (fi :: M.FloatInfo) :: C.FloatInfo where
  ToCrucibleFloatInfo M.HalfFloat   = C.HalfFloat
  ToCrucibleFloatInfo M.SingleFloat = C.SingleFloat
  ToCrucibleFloatInfo M.DoubleFloat = C.DoubleFloat
  ToCrucibleFloatInfo M.QuadFloat   = C.QuadFloat
  ToCrucibleFloatInfo M.X86_80Float = C.X86_80Float

-- | Convert Crucible float types into Macaw float types
type family FromCrucibleFloatInfo (fi :: C.FloatInfo) :: M.FloatInfo where
  FromCrucibleFloatInfo C.HalfFloat   = M.HalfFloat
  FromCrucibleFloatInfo C.SingleFloat = M.SingleFloat
  FromCrucibleFloatInfo C.DoubleFloat = M.DoubleFloat
  FromCrucibleFloatInfo C.QuadFloat   = M.QuadFloat
  FromCrucibleFloatInfo C.X86_80Float = M.X86_80Float

type family CtxToCrucibleType (mtp :: Ctx M.Type) :: Ctx C.CrucibleType where
  CtxToCrucibleType EmptyCtx   = EmptyCtx
  CtxToCrucibleType (c ::> tp) = CtxToCrucibleType c ::> ToCrucibleType tp

-- | Create the variables from a collection of registers.
macawAssignToCruc ::
  (forall tp . f tp -> g (ToCrucibleType tp)) ->
  Assignment f ctx ->
  Assignment g (CtxToCrucibleType ctx)
macawAssignToCruc f a =
  case a of
    Empty -> empty
    b :> x -> macawAssignToCruc f b :> f x

-- | Convert a 'Ctx.Assignment' of macaw values into a 'Ctx.Assignment' of Crucible values
macawAssignToCrucM :: Applicative m
                   => (forall tp . f tp -> m (g (ToCrucibleType tp)))
                   -> Assignment f ctx
                   -> m (Assignment g (CtxToCrucibleType ctx))
macawAssignToCrucM f a =
  case a of
    Empty -> pure empty
    b :> x -> (:>) <$> macawAssignToCrucM f b <*> f x

-- | Convert Macaw run-time type representatives into their Crucible equivalents
typeToCrucible :: M.TypeRepr tp -> C.TypeRepr (ToCrucibleType tp)
typeToCrucible tp =
  case tp of
    M.BoolTypeRepr  -> C.BoolRepr
    M.BVTypeRepr w  -> MM.LLVMPointerRepr w
    M.FloatTypeRepr fi -> C.FloatRepr $ floatInfoToCrucible fi
    M.TupleTypeRepr a -> C.StructRepr (typeListToCrucible a)

-- | Convert Macaw floating point run-time representatives into their Crucible equivalents
floatInfoToCrucible
  :: M.FloatInfoRepr fi -> C.FloatInfoRepr (ToCrucibleFloatInfo fi)
floatInfoToCrucible = \case
  M.HalfFloatRepr   -> knownRepr
  M.SingleFloatRepr -> knownRepr
  M.DoubleFloatRepr -> knownRepr
  M.QuadFloatRepr   -> knownRepr
  M.X86_80FloatRepr -> knownRepr

-- | Convert Crucible floating point run-time representatives into their Macaw equivalents
floatInfoFromCrucible
  :: C.FloatInfoRepr fi -> M.FloatInfoRepr (FromCrucibleFloatInfo fi)
floatInfoFromCrucible = \case
  C.HalfFloatRepr   -> knownRepr
  C.SingleFloatRepr -> knownRepr
  C.DoubleFloatRepr -> knownRepr
  C.QuadFloatRepr   -> knownRepr
  C.X86_80FloatRepr -> knownRepr
  fi ->
    error $ "Unsupported Crucible floating-point format in Macaw: " ++ show fi

typeListToCrucible ::
    P.List M.TypeRepr ctx ->
    Assignment C.TypeRepr (ToCrucibleTypeList ctx)
typeListToCrucible x =
  case x of
    P.Nil    -> Empty
    h P.:< r -> typeListToCrucible r :> typeToCrucible h

-- | Return the types associated with a register assignment.
typeCtxToCrucible ::
  Assignment M.TypeRepr ctx ->
  Assignment C.TypeRepr (CtxToCrucibleType ctx)
typeCtxToCrucible = macawAssignToCruc typeToCrucible

memReprToCrucible :: M.MemRepr tp -> C.TypeRepr (ToCrucibleType tp)
memReprToCrucible = typeToCrucible . M.typeRepr

------------------------------------------------------------------------
-- RegIndexMap

-- | Type family for architecture registers
--
-- This specifies the type of each register in the register file for a given architecture.  For example,
-- it might be something like
--
-- > EmptyCtx ::> BVType 64 ::> BVType 64 ::> BVType 32
--
-- For a hypothetical architecture with two 64 bit general purpose registers and
-- a single 32 bit flags register.
type family ArchRegContext (arch :: *) :: Ctx M.Type

-- | This relates an index from macaw to Crucible.
data IndexPair ctx tp = IndexPair
  { macawIndex    :: !(Index ctx tp)
  , crucibleIndex :: !(Index (CtxToCrucibleType ctx) (ToCrucibleType tp))
  }

-- | This extends the indices in the pair.
extendIndexPair :: IndexPair ctx tp -> IndexPair (ctx::>utp) tp
extendIndexPair (IndexPair i j) = IndexPair (extendIndex i) (extendIndex j)


type RegIndexMap arch = MapF (M.ArchReg arch) (IndexPair (ArchRegContext arch))

mkRegIndexMap :: OrdF r
              => Assignment r ctx
              -> Size (CtxToCrucibleType ctx)
              -> MapF r (IndexPair ctx)
mkRegIndexMap Empty _ = MapF.empty
mkRegIndexMap (a :> r) csz =
  case viewSize csz of
    IncSize csz0 ->
      let m = fmapF extendIndexPair (mkRegIndexMap a csz0)
          idx = IndexPair (nextIndex (size a)) (nextIndex csz0)
       in MapF.insert r idx m

------------------------------------------------------------------------
-- Misc types

-- | A Crucible value with a Macaw type.
data MacawCrucibleValue f tp = MacawCrucibleValue (f (ToCrucibleType tp))

instance FunctorFC MacawCrucibleValue where
  fmapFC f (MacawCrucibleValue v) = MacawCrucibleValue (f v)

instance FoldableFC MacawCrucibleValue where
  foldrFC f x (MacawCrucibleValue v) = f v x

instance TraversableFC MacawCrucibleValue where
  traverseFC f (MacawCrucibleValue v) = MacawCrucibleValue <$> f v

------------------------------------------------------------------------
-- CrucPersistentState

-- | State that needs to be persisted across block translations
data CrucPersistentState ids h s
   = CrucPersistentState
   { nonceGen :: NonceGenerator (ST h) s
     -- ^ Generator used to get fresh ids for Crucible atoms.
   , assignValueMap ::
      !(MapF (M.AssignId ids) (MacawCrucibleValue (CR.Atom s)))
     -- ^ Map Macaw assign id to associated Crucible value.
   }

-- | Initial crucible persistent state
initCrucPersistentState :: NonceGenerator (ST h) s
                        -> CrucPersistentState ids h s
initCrucPersistentState ng =
  CrucPersistentState
      { nonceGen       = ng
      , assignValueMap = MapF.empty
      }
