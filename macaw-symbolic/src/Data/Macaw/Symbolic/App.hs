{-
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wwarn #-}
module Data.Macaw.Symbolic.App where

import           Control.Lens
import           Control.Monad.ST
import           Control.Monad.State.Strict
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
import Data.String
import           Data.Text
import           Data.Word
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.FunctionHandle as C
import           Lang.Crucible.ProgramLoc as C
import qualified Lang.Crucible.Types as C

type family ToCrucibleType (mtp :: M.Type) :: C.CrucibleType where
  ToCrucibleType (M.BVType w) = C.BVType w
  ToCrucibleType M.BoolType   = C.BoolType

typeToCrucible :: M.TypeRepr tp -> C.TypeRepr (ToCrucibleType tp)
typeToCrucible tp =
  case tp of
    M.BoolTypeRepr -> C.BoolRepr
    M.BVTypeRepr w -> C.BVRepr w

memReprToCrucible :: M.MemRepr tp -> C.TypeRepr (ToCrucibleType tp)
memReprToCrucible = typeToCrucible . M.typeRepr

-- | A Crucible value with a Macaw type.
data WrappedAtom s tp = WrappedAtom (C.Atom s (ToCrucibleType tp))

type ArchConstraints arch
   = ( M.MemWidth (M.ArchAddrWidth arch)
     , OrdF (M.ArchReg arch)
     )

newtype SymbolicHandle f tp = SymbolicHandle (f (ToCrucibleType tp))

type ReadMemHandle arch = C.FnHandle (EmptyCtx ::> C.BVType (M.ArchAddrWidth arch))

-- | State used for generating blocks
data CrucGenState arch ids s
   = CrucGenState
   { archConstraints :: !(forall a . (ArchConstraints arch => a) -> a)
     -- ^ Typeclass constraints for architecture
   , archWidthRepr :: !(NatRepr (M.ArchAddrWidth arch))
     -- ^ Width of the architecture
   , handleAlloc :: !(C.HandleAllocator s)
     -- ^ Handle allocator
   , binaryPath :: !Text
     -- ^ Name of binary these blocks come from.
   , codeAddr :: !Word64
     -- ^ Address of this code
   , translateArchFn :: !(forall tp
                          . M.ArchFn arch ids tp
                          -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp)))
   , freshSymHandleMap :: !(MapF M.TypeRepr (SymbolicHandle (C.FnHandle EmptyCtx)))
     -- ^ Map type reprs to associated handle for creating symbolic values.
   , readMemHandleMap  :: !(MapF M.MemRepr (SymbolicHandle (ReadMemHandle arch)))
   , prevStmts :: ![C.Stmt s]
     -- ^ List of states in reverse order
   , valueCount :: !Int
     -- ^ Counter used to get fresh indices for Crucible atoms.
   , memSegmentMap :: !(Map M.SegmentIndex (C.Atom s (C.BVType (M.ArchAddrWidth arch))))
     -- ^ Map from segment indices to the Crucible value denoting the base.
   , regValueMap :: !(MapF (M.ArchReg arch) (WrappedAtom s))
     -- ^ Maps Macaw register initial values in block to associated Crucible value.
   , assignValueMap :: !(MapF (M.AssignId ids) (WrappedAtom s))
     -- ^ Map Macaw assign id to associated Crucible value.
   }

type CrucGen arch ids s = StateT (CrucGenState arch ids s) (ST s)


addStmt :: C.Stmt s -> CrucGen arch ids s ()
addStmt stmt = seq stmt $ do
  s <- get
  put $! s { prevStmts = stmt : prevStmts s }

freshValueIndex :: CrucGen arch ids s Int
freshValueIndex = do
  s <- get
  let cnt = valueCount s
  put  $! s { valueCount = cnt + 1 }
  pure $! cnt

-- | Evaluate the crucible app and return a reference to the result.
evalAtom :: C.AtomValue s ctp -> CrucGen arch ids s (C.Atom s ctp)
evalAtom av = do
  fname <- gets binaryPath
  addr  <- gets codeAddr
  let p = C.BinaryPos fname addr
  i <- freshValueIndex
  -- Make atom
  let atom = C.Atom { C.atomPosition = p
                    , C.atomId = i
                    , C.atomSource = C.Assigned
                    , C.typeOfAtom = C.typeOfAtomValue av
                    }
  addStmt $ C.DefineAtom atom av
  pure $! atom

-- | Evaluate the crucible app and return a reference to the result.
crucibleValue :: C.App (C.Atom s) ctp -> CrucGen arch ids s (C.Atom s ctp)
crucibleValue app = evalAtom (C.EvalApp app)

appToCrucible :: M.App (M.Value arch ids) tp
              -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
appToCrucible app =
  case app of
    M.Mux w c t f -> do
      crucibleValue =<<
        C.BVIte <$> valueToCrucible c
                <*> pure w
                <*> valueToCrucible t
                <*> valueToCrucible f
    _ -> undefined

valueToCrucible :: M.Value arch ids tp
                -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
valueToCrucible v = do
  cns <- gets archConstraints
  cns $ do
  case v of
    M.BVValue w c -> do
      crucibleValue (C.BVLit w c)
    M.BoolValue b -> do
      crucibleValue (C.BoolLit b)
    M.RelocatableValue w addr -> do
      let seg = M.addrSegment addr
      case M.segmentBase seg of
        Just base -> do
          crucibleValue (C.BVLit w (toInteger base + toInteger (addr^.M.addrOffset)))
        Nothing -> do
          let idx = M.segmentIndex seg
          segMap <- gets memSegmentMap
          case Map.lookup idx segMap of
            Just a -> pure a
            Nothing -> fail $ "internal: No Crucible address associated with segment."
    M.Initial r -> do
      regmap <- gets regValueMap
      case MapF.lookup r regmap of
        Just (WrappedAtom a) -> pure a
        Nothing -> fail $ "internal: Register is not bound."
    M.AssignedValue asgn -> do
      let idx = M.assignId asgn
      amap <- gets assignValueMap
      case MapF.lookup idx amap of
        Just (WrappedAtom r) -> pure r
        Nothing ->  fail "internal: Assignment id is not bound."

freshSymbolicHandle :: M.TypeRepr tp
                    -> CrucGen arch ids s (C.FnHandle EmptyCtx (ToCrucibleType tp))
freshSymbolicHandle repr = do
  hmap <- gets freshSymHandleMap
  case MapF.lookup repr hmap of
    Just (SymbolicHandle h) -> pure h
    Nothing -> do
      let fnm = case repr of
                  M.BoolTypeRepr -> "symbolicBool"
                  M.BVTypeRepr w -> fromString $ "symbolicBV" ++ show w
      halloc <- gets handleAlloc
      hndl <- lift $ C.mkHandle' halloc fnm Ctx.empty (typeToCrucible repr)
      modify $ \s -> s { freshSymHandleMap =
                           MapF.insert repr (SymbolicHandle hndl) (freshSymHandleMap s)
                       }
      pure $! hndl

runCall :: C.FnHandle args ret
        -> Ctx.Assignment (C.Atom s) args
        -> C.TypeRepr ret
        -> CrucGen arch ids s (C.Atom s ret)
runCall hndl args ret = do
  hatom <- crucibleValue (C.HandleLit hndl)
  evalAtom $ C.Call hatom args ret

freshSymbolic :: M.TypeRepr tp -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
freshSymbolic repr = do
  hndl <- freshSymbolicHandle repr
  runCall hndl Ctx.empty (typeToCrucible repr)

readMemHandle :: M.MemRepr tp
              -> CrucGen arch ids s (ReadMemHandle arch (ToCrucibleType tp))
readMemHandle repr = do
  hmap <- gets readMemHandleMap
  case MapF.lookup repr hmap of
    Just (SymbolicHandle r) -> pure r
    Nothing -> do
      cns <- gets archConstraints
      cns $ do
      halloc <- gets handleAlloc
      let fnm = case repr of
                  M.BVMemRepr w _ -> fromString $ "readWord" ++ show w
      wrepr <- gets archWidthRepr
      let argTypes = Ctx.empty Ctx.%> C.BVRepr wrepr
      hndl <- lift $ C.mkHandle' halloc fnm argTypes (memReprToCrucible repr)
      modify' $ \s ->
        s { readMemHandleMap = MapF.insert repr (SymbolicHandle hndl) (readMemHandleMap s) }
      pure hndl

readMem :: M.ArchAddrValue arch ids
        -> M.MemRepr tp
        -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
readMem addr repr = do
  hndl <- readMemHandle repr
  caddr <- valueToCrucible addr
  runCall hndl (Ctx.empty Ctx.%> caddr) (memReprToCrucible repr)

assignRhsToCrucible :: M.AssignRhs arch ids tp
                    -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
assignRhsToCrucible rhs =
  case rhs of
    M.EvalApp app -> appToCrucible app
    M.SetUndefined mrepr -> freshSymbolic mrepr
    M.ReadMem addr repr -> readMem addr repr
    M.EvalArchFn f _ -> do
      fn <- gets translateArchFn
      fn f

addMacawStmt :: M.Stmt arch ids -> CrucGen arch ids s ()
addMacawStmt stmt = do
  case stmt of
    M.AssignStmt asgn -> do
      let idx = M.assignId asgn
      a <- assignRhsToCrucible (M.assignRhs asgn)
      modify' $ \s -> s { assignValueMap = MapF.insert idx (WrappedAtom a) (assignValueMap s) }
    M.WriteMem addr repr val -> do
      undefined addr repr val
    M.PlaceHolderStmt vals msg -> do
      undefined vals msg
    M.Comment txt -> do
      undefined txt
    M.ExecArchStmt astmt -> do
      undefined astmt
