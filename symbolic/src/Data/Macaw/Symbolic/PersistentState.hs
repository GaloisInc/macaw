{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines the monad used to map Reopt blocks to Crucible.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
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
  , CtxToCrucibleType
  , ArchRegContext
  , typeToCrucible
  , typeCtxToCrucible
  , macawAssignToCrucM
  , memReprToCrucible
    -- * Register index map
  , RegIndexMap
  , mkRegIndexMap
  , IndexPair(..)
    -- * Values
  , MacawCrucibleValue(..)
  ) where


import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Types as M
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import qualified Data.Parameterized.List as P
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableF
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.LLVM.MemModel as MM

------------------------------------------------------------------------
-- Type mappings

type family ToCrucibleTypeList a (l :: [M.Type]) :: Ctx C.CrucibleType where
  ToCrucibleTypeList a '[]      = EmptyCtx
  ToCrucibleTypeList a (h ': l) = ToCrucibleTypeList a l ::> ToCrucibleType a h

type family ToCrucibleType a (tp :: M.Type) :: C.CrucibleType where
  ToCrucibleType a (M.BVType w)     = MM.LLVMPointerType w
  ToCrucibleType a ('M.TupleType l) = C.StructType (ToCrucibleTypeList a l)
  ToCrucibleType a M.BoolType       = C.BaseToType C.BaseBoolType


type family CtxToCrucibleType a (mtp :: Ctx M.Type) :: Ctx C.CrucibleType where
  CtxToCrucibleType a EmptyCtx   = EmptyCtx
  CtxToCrucibleType a (c ::> tp) = CtxToCrucibleType a c ::> ToCrucibleType a tp

-- | Create the variables from a collection of registers.
macawAssignToCruc :: p a ->
                    (forall tp . f tp -> g (ToCrucibleType a tp))
                  -> Assignment f ctx
                  -> Assignment g (CtxToCrucibleType a ctx)
macawAssignToCruc arch f a =
  case a of
    Empty -> empty
    b :> x -> macawAssignToCruc arch f b :> f x

-- | Create the variables from a collection of registers.
macawAssignToCrucM :: Applicative m
                   => p a ->
                      (forall tp . f tp -> m (g (ToCrucibleType a tp)))
                   -> Assignment f ctx
                   -> m (Assignment g (CtxToCrucibleType a ctx))
macawAssignToCrucM arch f a =
  case a of
    Empty -> pure empty
    b :> x -> (:>) <$> macawAssignToCrucM arch f b <*> f x

typeToCrucible :: p a -> M.TypeRepr tp -> C.TypeRepr (ToCrucibleType a tp)
typeToCrucible arch tp =
  case tp of
    M.BoolTypeRepr  -> C.BoolRepr
    M.BVTypeRepr w  -> MM.LLVMPointerRepr w
    M.TupleTypeRepr a -> C.StructRepr (typeListToCrucible arch a)

typeListToCrucible ::
  p a -> P.List M.TypeRepr ctx ->
    Assignment C.TypeRepr (ToCrucibleTypeList a ctx)
typeListToCrucible arch x =
  case x of
    P.Nil    -> Empty
    h P.:< r -> typeListToCrucible arch r :> typeToCrucible arch h

-- Return the types associated with a register assignment.
typeCtxToCrucible ::
  p a ->
  Assignment M.TypeRepr ctx ->
  Assignment C.TypeRepr (CtxToCrucibleType a ctx)
typeCtxToCrucible arch = macawAssignToCruc arch (typeToCrucible arch)

memReprToCrucible :: p a -> M.MemRepr tp -> C.TypeRepr (ToCrucibleType a tp)
memReprToCrucible a = typeToCrucible a . M.typeRepr

------------------------------------------------------------------------
-- RegIndexMap

-- | Type family for architecture registers
type family ArchRegContext (arch :: *) :: Ctx M.Type

-- | This relates an index from macaw to Crucible.
data IndexPair a ctx tp = IndexPair
  { macawIndex    :: !(Index ctx tp)
  , crucibleIndex :: !(Index (CtxToCrucibleType a ctx) (ToCrucibleType a tp))
  }

-- | This extends the indices in the pair.
extendIndexPair :: IndexPair a ctx tp -> IndexPair a (ctx::>utp) tp
extendIndexPair (IndexPair i j) = IndexPair (extendIndex i) (extendIndex j)


type RegIndexMap arch = MapF (M.ArchReg arch)
                             (IndexPair arch (ArchRegContext arch))

mkRegIndexMap :: OrdF r
              => Assignment r ctx
              -> Size (CtxToCrucibleType a ctx)
              -> MapF r (IndexPair a ctx)
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
data MacawCrucibleValue a f tp = MacawCrucibleValue (f (ToCrucibleType a tp))

------------------------------------------------------------------------
-- CrucPersistentState

-- | State that needs to be persisted across block translations
data CrucPersistentState a ids s
   = CrucPersistentState
   { valueCount :: !Int
     -- ^ Counter used to get fresh indices for Crucible atoms.
   , assignValueMap ::
      !(MapF (M.AssignId ids) (MacawCrucibleValue a (CR.Atom s)))
     -- ^ Map Macaw assign id to associated Crucible value.
   }

-- | Initial crucible persistent state
initCrucPersistentState :: forall ids s a . Int -> CrucPersistentState a ids s
initCrucPersistentState argCount =
  CrucPersistentState
      { -- Count initial arguments in valie
        valueCount     = argCount
      , assignValueMap = MapF.empty
      }
