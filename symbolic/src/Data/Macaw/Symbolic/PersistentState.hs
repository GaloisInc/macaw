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
  , handleMapLens
  , seenBlockMapLens
    -- * Types
  , ToCrucibleBaseType
  , ToCrucibleType
  , ArchAddrCrucibleType
  , CtxToCrucibleType
  , ArchRegContext
  , ArchCrucibleRegTypes
  , ArchRegStruct
  , MacawFunctionArgs
  , MacawFunctionResult
  , typeToCrucibleBase
  , typeToCrucible
  , typeCtxToCrucible
  , regStructRepr
  , macawAssignToCrucM
    -- * CrucGenContext
  , CrucGenContext(..)
  , archWidthRepr
  , MemSegmentMap
    -- * Handle set
  , UsedHandleSet
  , HandleId(..)
  , handleIdName
  , handleIdArgTypes
  , handleIdRetType
  , HandleVal(..)
    -- * Register index map
  , RegIndexMap
  , mkRegIndexMap
  , IndexPair(..)
    -- * Values
  , MacawCrucibleValue(..)
    -- * Blocks
  , CrucSeenBlockMap
  ) where

import           Control.Lens
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Memory as M
import qualified Data.Macaw.Types as M
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.String
import           Data.Text (Text)
import           Data.Word
import qualified Lang.Crucible.CFG.Common as C
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.FunctionName as C
import qualified Lang.Crucible.Types as C

------------------------------------------------------------------------
-- Type mappings

type family ToCrucibleBaseType (mtp :: M.Type) :: C.BaseType where
  ToCrucibleBaseType (M.BVType w) = C.BaseBVType w
  ToCrucibleBaseType M.BoolType   = C.BaseBoolType

type ToCrucibleType tp = C.BaseToType (ToCrucibleBaseType tp)

type family CtxToCrucibleType (mtp :: Ctx M.Type) :: Ctx C.CrucibleType where
  CtxToCrucibleType EmptyCtx   = EmptyCtx
  CtxToCrucibleType (c ::> tp) = CtxToCrucibleType c ::> ToCrucibleType tp

-- | Type family for arm registers
type family ArchRegContext (arch :: *) :: Ctx M.Type

-- | List of crucible types for architecture.
type ArchCrucibleRegTypes (arch :: *) = CtxToCrucibleType (ArchRegContext arch)

type ArchRegStruct (arch :: *) = C.StructType (ArchCrucibleRegTypes arch)
type MacawFunctionArgs arch = EmptyCtx ::> ArchRegStruct arch
type MacawFunctionResult arch = ArchRegStruct arch

type ArchAddrCrucibleType arch = C.BVType (M.ArchAddrWidth arch)

typeToCrucibleBase :: M.TypeRepr tp -> C.BaseTypeRepr (ToCrucibleBaseType tp)
typeToCrucibleBase tp =
  case tp of
    M.BoolTypeRepr -> C.BaseBoolRepr
    M.BVTypeRepr w -> C.BaseBVRepr w

typeToCrucible :: M.TypeRepr tp -> C.TypeRepr (ToCrucibleType tp)
typeToCrucible = C.baseToType . typeToCrucibleBase


-- | Create the variables from a collection of registers.
macawAssignToCruc :: (forall tp . f tp -> g (ToCrucibleType tp))
                  -> Ctx.Assignment f ctx
                  -> Ctx.Assignment g (CtxToCrucibleType ctx)
macawAssignToCruc f a =
  case Ctx.view a of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend b x -> macawAssignToCruc f b Ctx.%> f x

-- | Create the variables from a collection of registers.
macawAssignToCrucM :: Applicative m
                   => (forall tp . f tp -> m (g (ToCrucibleType tp)))
                   -> Ctx.Assignment f ctx
                   -> m (Ctx.Assignment g (CtxToCrucibleType ctx))
macawAssignToCrucM f a =
  case Ctx.view a of
    Ctx.AssignEmpty -> pure Ctx.empty
    Ctx.AssignExtend b x -> (Ctx.%>) <$> macawAssignToCrucM f b <*> f x


-- Return the types associated with a register assignment.
typeCtxToCrucible :: Ctx.Assignment M.TypeRepr ctx
                  -> Ctx.Assignment C.TypeRepr (CtxToCrucibleType ctx)
typeCtxToCrucible = macawAssignToCruc typeToCrucible

memReprToCrucible :: M.MemRepr tp -> C.TypeRepr (ToCrucibleType tp)
memReprToCrucible = typeToCrucible . M.typeRepr

------------------------------------------------------------------------
-- RegIndexMap

-- | This relates an index from macaw to Crucible.
data IndexPair ctx tp = IndexPair { macawIndex    :: !(Ctx.Index ctx tp)
                                  , crucibleIndex :: !(Ctx.Index (CtxToCrucibleType ctx) (ToCrucibleType tp))
                                  }

-- | This extends the indices in the pair.
extendIndexPair :: IndexPair ctx tp -> IndexPair (ctx::>utp) tp
extendIndexPair (IndexPair i j) = IndexPair (Ctx.extendIndex i) (Ctx.extendIndex j)


type RegIndexMap arch = MapF (M.ArchReg arch) (IndexPair (ArchRegContext arch))

mkRegIndexMap :: OrdF r
              => Ctx.Assignment r ctx
              -> Ctx.Size (CtxToCrucibleType ctx)
              -> MapF r (IndexPair ctx)
mkRegIndexMap r0 csz =
  case (Ctx.view r0, Ctx.viewSize csz) of
    (Ctx.AssignEmpty, _) -> MapF.empty
    (Ctx.AssignExtend a r, Ctx.IncSize csz0) ->
      let m = fmapF extendIndexPair (mkRegIndexMap a csz0)
          idx = IndexPair (Ctx.nextIndex (Ctx.size a)) (Ctx.nextIndex csz0)
       in MapF.insert r idx m

------------------------------------------------------------------------
-- CrucGenContext

type ArchConstraints arch
   = ( M.MemWidth (M.ArchAddrWidth arch)
     , OrdF (M.ArchReg arch)
     , M.HasRepr (M.ArchReg arch) M.TypeRepr
     )

-- | Map from indices of segments without a fixed base address to a
-- global variable storing the base address.
type MemSegmentMap w = Map M.RegionIndex (C.GlobalVar (C.BVType w))

--- | Information that does not change during generating Crucible from MAcaw
data CrucGenContext arch ids s
   = CrucGenContext
   { archConstraints :: !(forall a . (ArchConstraints arch => a) -> a)
     -- ^ Typeclass constraints for architecture
   , macawRegAssign :: !(Ctx.Assignment (M.ArchReg arch) (ArchRegContext arch))
     -- ^ Assignment from register to the context
   , regIndexMap :: !(RegIndexMap arch)
   , handleAlloc :: !(C.HandleAllocator s)
     -- ^ Handle allocator
   , binaryPath :: !Text
     -- ^ Name of binary these blocks come from.
   , macawIndexToLabelMap :: !(Map Word64 (CR.Label s))
     -- ^ Map from block indices to the associated label.
   , memBaseAddrMap :: !(MemSegmentMap (M.ArchAddrWidth arch))
     -- ^ Map from indices of segments without a fixed base address to a global
     -- variable storing the base address.
   }

archWidthRepr :: forall arch ids s . CrucGenContext arch ids s -> NatRepr (M.ArchAddrWidth arch)
archWidthRepr ctx = archConstraints ctx $
  let arepr :: M.AddrWidthRepr (M.ArchAddrWidth arch)
      arepr = M.addrWidthRepr arepr
   in M.addrWidthNatRepr arepr


regStructRepr :: CrucGenContext arch ids s -> C.TypeRepr (ArchRegStruct arch)
regStructRepr ctx = archConstraints ctx $
  C.StructRepr (typeCtxToCrucible (fmapFC M.typeRepr (macawRegAssign ctx)))

------------------------------------------------------------------------
-- Handle-related definitions

-- | An identifier for a Handle needed to map from Reopt to Crucible
data HandleId arch (ftp :: (Ctx C.CrucibleType, C.CrucibleType)) where
  MkFreshSymId :: !(M.TypeRepr tp)
                   -> HandleId arch '(EmptyCtx, ToCrucibleType tp)
  ReadMemId  :: !(M.MemRepr tp)
             -> HandleId arch
                           '( EmptyCtx ::> ArchAddrCrucibleType arch
                            , ToCrucibleType tp
                            )
  WriteMemId  :: !(M.MemRepr tp)
              -> HandleId arch
                          '( EmptyCtx ::> ArchAddrCrucibleType arch ::> ToCrucibleType tp
                           , C.UnitType
                           )
  SyscallId :: HandleId arch '(EmptyCtx ::> ArchRegStruct arch, ArchRegStruct arch)

instance TestEquality (HandleId arch) where
  testEquality x y = orderingF_refl (compareF x y)

instance OrdF (HandleId arch) where
  compareF (MkFreshSymId xr) (MkFreshSymId yr) = lexCompareF xr yr $ EQF
  compareF MkFreshSymId{} _ = LTF
  compareF _ MkFreshSymId{} = GTF

  compareF (ReadMemId xr) (ReadMemId yr) = lexCompareF xr yr $ EQF
  compareF ReadMemId{} _ = LTF
  compareF _ ReadMemId{} = GTF

  compareF (WriteMemId xr) (WriteMemId yr) = lexCompareF xr yr $ EQF
  compareF WriteMemId{} _ = LTF
  compareF _ WriteMemId{} = GTF

  compareF SyscallId SyscallId = EQF

handleIdName :: HandleId arch ftp -> C.FunctionName
handleIdName h =
  case h of
    MkFreshSymId repr ->
      case repr of
        M.BoolTypeRepr -> "symbolicBool"
        M.BVTypeRepr w -> fromString $ "symbolicBV" ++ show w
    ReadMemId (M.BVMemRepr w _) ->
      fromString $ "readMem" ++ show (8 * natValue w)
    WriteMemId (M.BVMemRepr w _) ->
      fromString $ "writeMem" ++ show (8 * natValue w)
    SyscallId -> "syscall"

handleIdArgTypes :: CrucGenContext arch ids s
                 -> HandleId arch '(args, ret)
                 -> Ctx.Assignment C.TypeRepr args
handleIdArgTypes ctx h =
  case h of
    MkFreshSymId _repr -> Ctx.empty
    ReadMemId _repr -> archConstraints ctx $
      Ctx.empty Ctx.%> C.BVRepr (archWidthRepr ctx)
    WriteMemId repr -> archConstraints ctx $
      Ctx.empty Ctx.%> C.BVRepr (archWidthRepr ctx)
                Ctx.%> memReprToCrucible repr
    SyscallId ->
      Ctx.empty Ctx.%> regStructRepr ctx

handleIdRetType :: CrucGenContext arch ids s
                -> HandleId arch '(args, ret)
                -> C.TypeRepr ret
handleIdRetType ctx h =
  case h of
    MkFreshSymId repr -> typeToCrucible repr
    ReadMemId  repr -> memReprToCrucible repr
    WriteMemId _ -> C.UnitRepr
    SyscallId -> regStructRepr ctx


-- | A particular handle in the UsedHandleSet
data HandleVal (ftp :: (Ctx C.CrucibleType, C.CrucibleType)) =
  forall args res . (ftp ~ '(args, res)) => HandleVal !(C.FnHandle args res)


-- | This  getting information about what handles are used
type UsedHandleSet arch = MapF (HandleId arch) HandleVal

------------------------------------------------------------------------
-- Misc types

-- | A Crucible value with a Macaw type.
data MacawCrucibleValue f tp = MacawCrucibleValue (f (ToCrucibleType tp))

--  | Map from block indices to the associated crucible block.
type CrucSeenBlockMap s arch = Map Word64 (CR.Block s (MacawFunctionResult arch))

------------------------------------------------------------------------
-- CrucPersistentState

-- | State that needs to be persisted across block translations
data CrucPersistentState arch ids s
   = CrucPersistentState
   { handleMap :: !(UsedHandleSet arch)
     -- ^ Handles found so far
   , valueCount :: !Int
     -- ^ Counter used to get fresh indices for Crucible atoms.
   , assignValueMap :: !(MapF (M.AssignId ids) (MacawCrucibleValue (CR.Atom s)))
     -- ^ Map Macaw assign id to associated Crucible value.
   , seenBlockMap :: !(CrucSeenBlockMap s arch)
     -- ^ Map Macaw block indices to the associated crucible block
   }

-- | Initial crucible persistent state
initCrucPersistentState :: forall arch ids s . CrucPersistentState arch ids s
initCrucPersistentState =
  -- Infer number of arguments to function so that we have values skip inputs.
  let argCount :: Ctx.Size (MacawFunctionArgs arch)
      argCount = Ctx.knownSize
   in CrucPersistentState
      { handleMap      = MapF.empty
      , valueCount     = Ctx.sizeInt argCount
      , assignValueMap = MapF.empty
      , seenBlockMap   = Map.empty
      }

handleMapLens :: Simple Lens (CrucPersistentState arch ids s) (UsedHandleSet arch)
handleMapLens = lens handleMap (\s v -> s { handleMap = v })

seenBlockMapLens :: Simple Lens (CrucPersistentState arch ids s) (CrucSeenBlockMap s arch)
seenBlockMapLens = lens seenBlockMap (\s v -> s { seenBlockMap = v })
