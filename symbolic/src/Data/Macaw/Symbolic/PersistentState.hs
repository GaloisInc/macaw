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

import           Control.Lens hiding (Index, (:>), Empty)
import           Data.List (intercalate)
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Memory as M
import qualified Data.Macaw.Types as M
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import qualified Data.Parameterized.List as P
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

type family ToCrucibleBaseTypeList (l :: [M.Type]) :: Ctx C.BaseType where
  ToCrucibleBaseTypeList '[] = EmptyCtx
  ToCrucibleBaseTypeList (h ': l) = ToCrucibleBaseTypeList l ::> ToCrucibleBaseType h

type family ToCrucibleBaseType (mtp :: M.Type) :: C.BaseType where
  ToCrucibleBaseType M.BoolType   = C.BaseBoolType
  ToCrucibleBaseType (M.BVType w) = C.BaseBVType w
  ToCrucibleBaseType ('M.TupleType l) = C.BaseStructType (ToCrucibleBaseTypeList l)

type family CtxToCrucibleBaseType (mtp :: Ctx M.Type) :: Ctx C.BaseType where
  CtxToCrucibleBaseType EmptyCtx   = EmptyCtx
  CtxToCrucibleBaseType (c ::> tp) = CtxToCrucibleBaseType c ::> ToCrucibleBaseType tp

type ToCrucibleType tp = C.BaseToType (ToCrucibleBaseType tp)

type family CtxToCrucibleType (mtp :: Ctx M.Type) :: Ctx C.CrucibleType where
  CtxToCrucibleType EmptyCtx   = EmptyCtx
  CtxToCrucibleType (c ::> tp) = CtxToCrucibleType c ::> ToCrucibleType tp

-- | Create the variables from a collection of registers.
macawAssignToCruc :: (forall tp . f tp -> g (ToCrucibleType tp))
                  -> Assignment f ctx
                  -> Assignment g (CtxToCrucibleType ctx)
macawAssignToCruc f a =
  case a of
    Empty -> empty
    b :> x -> macawAssignToCruc f b :> f x

-- | Create the variables from a collection of registers.
macawAssignToCrucM :: Applicative m
                   => (forall tp . f tp -> m (g (ToCrucibleType tp)))
                   -> Assignment f ctx
                   -> m (Assignment g (CtxToCrucibleType ctx))
macawAssignToCrucM f a =
  case a of
    Empty -> pure empty
    b :> x -> (:>) <$> macawAssignToCrucM f b <*> f x

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
    M.BoolTypeRepr  -> C.BaseBoolRepr
    M.BVTypeRepr w  -> C.BaseBVRepr w
    M.TupleTypeRepr a -> C.BaseStructRepr (typeListToCrucibleBase a)

typeListToCrucibleBase :: P.List M.TypeRepr ctx -> Assignment C.BaseTypeRepr (ToCrucibleBaseTypeList ctx)
typeListToCrucibleBase P.Nil = Empty
typeListToCrucibleBase (h P.:< r) = typeListToCrucibleBase r :> typeToCrucibleBase h

typeToCrucible :: M.TypeRepr tp -> C.TypeRepr (ToCrucibleType tp)
typeToCrucible = C.baseToType . typeToCrucibleBase

-- Return the types associated with a register assignment.
typeCtxToCrucible :: Assignment M.TypeRepr ctx
                  -> Assignment C.TypeRepr (CtxToCrucibleType ctx)
typeCtxToCrucible = macawAssignToCruc typeToCrucible

memReprToCrucible :: M.MemRepr tp -> C.TypeRepr (ToCrucibleType tp)
memReprToCrucible = typeToCrucible . M.typeRepr

------------------------------------------------------------------------
-- RegIndexMap

-- | This relates an index from macaw to Crucible.
data IndexPair ctx tp = IndexPair { macawIndex    :: !(Index ctx tp)
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
data CrucGenContext arch s
   = CrucGenContext
   { archConstraints :: !(forall a . (ArchConstraints arch => a) -> a)
     -- ^ Typeclass constraints for architecture
   , macawRegAssign :: !(Assignment (M.ArchReg arch) (ArchRegContext arch))
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

archWidthRepr :: forall arch s . CrucGenContext arch s -> M.AddrWidthRepr (M.ArchAddrWidth arch)
archWidthRepr ctx = archConstraints ctx $ M.addrWidthRepr (archWidthRepr ctx)

regStructRepr :: CrucGenContext arch s -> C.TypeRepr (ArchRegStruct arch)
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
--  compareF WriteMemId{} _ = LTF
--  compareF _ WriteMemId{} = GTF

typeName :: M.TypeRepr tp -> String
typeName M.BoolTypeRepr = "Bool"
typeName (M.BVTypeRepr w) = "BV" ++ show w
typeName (M.TupleTypeRepr ctx) = "(" ++ intercalate "," (toListFC typeName ctx)  ++ ")"

endName :: M.Endianness -> String
endName M.LittleEndian = "le"
endName M.BigEndian = "be"

handleIdName :: HandleId arch ftp -> C.FunctionName
handleIdName h =
  case h of
    MkFreshSymId repr ->
      fromString $ "symbolic_" ++ typeName repr
    ReadMemId (M.BVMemRepr w end) ->
      fromString $ "readMem_" ++ show (8 * natValue w) ++ "_" ++ endName end
    WriteMemId (M.BVMemRepr w end) ->
      fromString $ "writeMem_" ++ show (8 * natValue w) ++ "_" ++ endName end

handleIdArgTypes :: CrucGenContext arch s
                 -> HandleId arch '(args, ret)
                 -> Assignment C.TypeRepr args
handleIdArgTypes ctx h =
  case h of
    MkFreshSymId _repr -> empty
    ReadMemId _repr -> archConstraints ctx $
      empty :> C.BVRepr (M.addrWidthNatRepr (archWidthRepr ctx))
    WriteMemId repr -> archConstraints ctx $
      empty :> C.BVRepr (M.addrWidthNatRepr (archWidthRepr ctx))
            :> memReprToCrucible repr

handleIdRetType :: HandleId arch '(args, ret)
                -> C.TypeRepr ret
handleIdRetType h =
  case h of
    MkFreshSymId repr -> typeToCrucible repr
    ReadMemId  repr -> memReprToCrucible repr
    WriteMemId _ -> C.UnitRepr

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
  let argCount :: Size (MacawFunctionArgs arch)
      argCount = knownSize
   in CrucPersistentState
      { handleMap      = MapF.empty
      , valueCount     = sizeInt argCount
      , assignValueMap = MapF.empty
      , seenBlockMap   = Map.empty
      }

handleMapLens :: Simple Lens (CrucPersistentState arch ids s) (UsedHandleSet arch)
handleMapLens = lens handleMap (\s v -> s { handleMap = v })

seenBlockMapLens :: Simple Lens (CrucPersistentState arch ids s) (CrucSeenBlockMap s arch)
seenBlockMapLens = lens seenBlockMap (\s v -> s { seenBlockMap = v })
