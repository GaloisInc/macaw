{-
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.FunctionHandle as C
import           Lang.Crucible.ProgramLoc as C
import qualified Lang.Crucible.Types as C

type family ArchRegContext (arch :: *) :: Ctx C.CrucibleType

type ArchRegStruct (arch :: *) = C.StructType (ArchRegContext arch)

type MacawFunctionArgs arch = EmptyCtx ::> ArchRegStruct arch
type MacawFunctionResult arch = ArchRegStruct arch

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

type ArchAddrCrucibleType arch = C.BVType (M.ArchAddrWidth arch)

-- | Type
type ReadMemHandle arch = C.FnHandle (EmptyCtx ::> ArchAddrCrucibleType arch)

type WriteMemHandle arch tp
   = C.FnHandle (EmptyCtx ::> ArchAddrCrucibleType arch ::> tp) C.UnitType

newtype WriteMemWrapper arch tp = WriteMemWrapper (WriteMemHandle arch (ToCrucibleType tp))

type FreshSymHandleMap = MapF M.TypeRepr (SymbolicHandle (C.FnHandle EmptyCtx))

type ReadMemHandleMap  arch = MapF M.MemRepr (SymbolicHandle (ReadMemHandle arch))
type WriteMemHandleMap arch = MapF M.MemRepr (WriteMemWrapper arch)

-- | Structure for getitng information about what handles are used
data CrucGenHandles arch
  = CrucGenHandles
  { freshSymHandleMap :: !FreshSymHandleMap
    -- ^ Map type reprs to associated handle for creating symbolic values.
  , readMemHandleMap  :: !(ReadMemHandleMap arch)
    -- ^ Maps memory repr to symbolic handle for reading memory.
  , writeMemHandleMap :: !(WriteMemHandleMap arch)
    -- ^ Maps mem repr to function for writing to memory.
  }

freshSymHandleMapLens :: Simple Lens (CrucGenHandles arch) FreshSymHandleMap
freshSymHandleMapLens = lens freshSymHandleMap (\s v -> s { freshSymHandleMap = v})

readMemHandleMapLens :: Simple Lens (CrucGenHandles arch) (ReadMemHandleMap arch)
readMemHandleMapLens = lens readMemHandleMap (\s v -> s { readMemHandleMap = v})

writeMemHandleMapLens :: Simple Lens (CrucGenHandles arch) (WriteMemHandleMap arch)
writeMemHandleMapLens = lens writeMemHandleMap (\s v -> s { writeMemHandleMap = v})

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
     -- ^ Function for translating an architecture specific function
   , translateArchStmt :: !(M.ArchStmt arch ids -> CrucGen arch ids s ())
     -- ^ Function for translating an architecture specific statement.
   , blockLabel :: (C.Label s)
     -- ^ Label for this block we are tranlating
   , handleMap :: !(CrucGenHandles arch)
     -- ^ Handles found so far
   , prevStmts :: ![C.Posd (C.Stmt s)]
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

handleMapLens :: Simple Lens (CrucGenState arch ids s) (CrucGenHandles arch)
handleMapLens = lens handleMap (\s v -> s { handleMap = v })

data CrucGenResult arch ids s
   = CrucGenResult
   { resHandleMap :: !(CrucGenHandles arch)
   , resBlock :: !(C.Block s (MacawFunctionResult arch))
   }

newtype CrucGen arch ids s r
   = CrucGen { unContGen
               :: CrucGenState arch ids s
                  -> (CrucGenState arch ids s -> r -> ST s (CrucGenResult arch ids s))
                  -> ST s (CrucGenResult arch ids s)
             }

instance Functor (CrucGen arch ids s) where
  fmap f m = CrucGen $ \s0 cont -> unContGen m s0 $ \s1 v -> cont s1 (f v)

instance Applicative (CrucGen arch ids s) where
  pure r = CrucGen $ \s cont -> cont s r
  mf <*> ma = CrucGen $ \s0 cont -> unContGen mf s0
                      $ \s1 f -> unContGen ma s1
                      $ \s2 a -> cont s2 (f a)

instance Monad (CrucGen arch ids s) where
  m >>= h = CrucGen $ \s0 cont -> unContGen m s0 $ \s1 r -> unContGen (h r) s1 cont

instance MonadState (CrucGenState arch ids s) (CrucGen arch ids s) where
  get = CrucGen $ \s cont -> cont s s
  put s = CrucGen $ \_ cont -> cont s ()

liftST :: ST s r -> CrucGen arch ids s r
liftST m = CrucGen $ \s cont -> m >>= cont s

getPos :: CrucGen arch ids s C.Position
getPos = undefined

addStmt :: C.Stmt s -> CrucGen arch ids s ()
addStmt stmt = seq stmt $ do
  p <- getPos
  s <- get
  let pstmt = C.Posd p stmt
  seq pstmt $ do
  put $! s { prevStmts = pstmt : prevStmts s }

addTermStmt :: C.TermStmt s (MacawFunctionResult arch)
            -> CrucGen arch ids s a
addTermStmt tstmt = do
  termPos <- getPos
  CrucGen $ \s _ -> do
  let lbl = C.LabelID (blockLabel s)
  let stmts = Seq.fromList (reverse (prevStmts s))
  let term = C.Posd termPos tstmt
  let blk = C.mkBlock lbl Set.empty stmts term
  let res = CrucGenResult
          { resHandleMap = handleMap s
          , resBlock = blk
          }
  pure $! res

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
  hmap <- use $ handleMapLens . freshSymHandleMapLens
  case MapF.lookup repr hmap of
    Just (SymbolicHandle h) -> pure h
    Nothing -> do
      let fnm = case repr of
                  M.BoolTypeRepr -> "symbolicBool"
                  M.BVTypeRepr w -> fromString $ "symbolicBV" ++ show w
      halloc <- gets handleAlloc
      hndl <- liftST $ C.mkHandle' halloc fnm Ctx.empty (typeToCrucible repr)
      handleMapLens . freshSymHandleMapLens %= MapF.insert repr (SymbolicHandle hndl)
      pure $! hndl

readMemHandle :: M.MemRepr tp
              -> CrucGen arch ids s (ReadMemHandle arch (ToCrucibleType tp))
readMemHandle repr = do
  hmap <- use $ handleMapLens . readMemHandleMapLens
  case MapF.lookup repr hmap of
    Just (SymbolicHandle r) -> pure r
    Nothing -> do
      cns <- gets archConstraints
      cns $ do
      halloc <- gets handleAlloc
      let fnm = case repr of
                  M.BVMemRepr w _ -> fromString $ "readWord" ++ show (8 * natValue w)
      wrepr <- gets archWidthRepr
      let argTypes = Ctx.empty Ctx.%> C.BVRepr wrepr
      hndl <- liftST $ C.mkHandle' halloc fnm argTypes (memReprToCrucible repr)
      handleMapLens . readMemHandleMapLens %= MapF.insert repr (SymbolicHandle hndl)
      pure hndl

writeMemHandle :: M.MemRepr tp
               -> CrucGen arch ids s (WriteMemHandle arch (ToCrucibleType tp))
writeMemHandle repr = do
  hmap <- use $ handleMapLens . writeMemHandleMapLens
  case MapF.lookup repr hmap of
    Just (WriteMemWrapper r) -> pure r
    Nothing -> do
      cns <- gets archConstraints
      cns $ do
      halloc <- gets handleAlloc
      let fnm = case repr of
                  M.BVMemRepr w _ -> fromString $ "readWord" ++ show (8 * natValue w)
      wrepr <- gets archWidthRepr
      let argTypes = Ctx.empty Ctx.%> C.BVRepr wrepr Ctx.%> memReprToCrucible repr
      hndl <- liftST $ C.mkHandle' halloc fnm argTypes C.UnitRepr
      handleMapLens . writeMemHandleMapLens %= MapF.insert repr (WriteMemWrapper hndl)
      pure hndl

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


readMem :: M.ArchAddrValue arch ids
        -> M.MemRepr tp
        -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
readMem addr repr = do
  hndl <- readMemHandle repr
  caddr <- valueToCrucible addr
  runCall hndl (Ctx.empty Ctx.%> caddr) (memReprToCrucible repr)

writeMem :: M.ArchAddrValue arch ids
        -> M.MemRepr tp
        -> M.Value arch ids tp
        -> CrucGen arch ids s ()
writeMem addr repr val = do
  hndl <- writeMemHandle repr
  caddr <- valueToCrucible addr
  cval  <- valueToCrucible val
  let args = Ctx.empty Ctx.%> caddr Ctx.%> cval
  void $ runCall hndl args C.UnitRepr

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
      writeMem addr repr val
    M.PlaceHolderStmt _vals msg -> do
      cmsg <- crucibleValue (C.TextLit (Text.pack msg))
      addTermStmt (C.ErrorStmt cmsg)
    M.Comment _txt -> do
      pure ()
    M.ExecArchStmt astmt -> do
      f <- gets translateArchStmt
      f astmt
