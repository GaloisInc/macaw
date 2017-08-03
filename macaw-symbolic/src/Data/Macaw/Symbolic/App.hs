{-
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wwarn #-}
module Data.Macaw.Symbolic.App
  ( CrucGenHandles(..)
  , emptyCrucGenHandles
  , CrucGenContext(..)
  , CrucPersistentState(..)
  , CrucSeenBlockMap
  , CtxToCrucibleType
  , ArchRegContext
  , MacawFunctionArgs
  , MacawFunctionResult
  , typeToCrucible
  , typeToCrucibleBase
  , addMacawBlock
  ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.ST
import           Control.Monad.State.Strict
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.CFG.Block as M
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

type family ToCrucibleBaseType (mtp :: M.Type) :: C.BaseType where
  ToCrucibleBaseType (M.BVType w) = C.BaseBVType w
  ToCrucibleBaseType M.BoolType   = C.BaseBoolType


type ToCrucibleType tp = C.BaseToType (ToCrucibleBaseType tp)

type family CtxToCrucibleType (mtp :: Ctx M.Type) :: Ctx C.CrucibleType where
  CtxToCrucibleType EmptyCtx   = EmptyCtx
  CtxToCrucibleType (c ::> tp) = CtxToCrucibleType c ::> ToCrucibleType tp

-- | Type family for arm registe
type family ArchRegContext (arch :: *) :: Ctx M.Type

type ArchRegStruct (arch :: *) = C.StructType (CtxToCrucibleType (ArchRegContext arch))

type MacawFunctionArgs arch = EmptyCtx ::> ArchRegStruct arch
type MacawFunctionResult arch = ArchRegStruct arch

typeToCrucibleBase :: M.TypeRepr tp -> C.BaseTypeRepr (ToCrucibleBaseType tp)
typeToCrucibleBase tp =
  case tp of
    M.BoolTypeRepr -> C.BaseBoolRepr
    M.BVTypeRepr w -> C.BaseBVRepr w

typeToCrucible :: M.TypeRepr tp -> C.TypeRepr (ToCrucibleType tp)
typeToCrucible = C.baseToType . typeToCrucibleBase

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

-- | Type of a function that reads memory
type ReadMemHandle arch = C.FnHandle (EmptyCtx ::> ArchAddrCrucibleType arch)

type WriteMemHandle arch tp
   = C.FnHandle (EmptyCtx ::> ArchAddrCrucibleType arch ::> tp) C.UnitType

newtype WriteMemWrapper arch tp = WriteMemWrapper (WriteMemHandle arch (ToCrucibleType tp))

type FreshSymHandleMap = MapF M.TypeRepr (SymbolicHandle (C.FnHandle EmptyCtx))

type ReadMemHandleMap  arch = MapF M.MemRepr (SymbolicHandle (ReadMemHandle arch))
type WriteMemHandleMap arch = MapF M.MemRepr (WriteMemWrapper arch)

-- | Structure for getting information about what handles are used
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

emptyCrucGenHandles :: CrucGenHandles arch
emptyCrucGenHandles =
  CrucGenHandles { freshSymHandleMap = MapF.empty
                 , readMemHandleMap = MapF.empty
                 , writeMemHandleMap = MapF.empty
                 }

data CrucGenContext arch ids s
   = CrucGenContext
   { archConstraints :: !(forall a . (ArchConstraints arch => a) -> a)
     -- ^ Typeclass constraints for architecture
   , translateArchFn :: !(forall tp
                          . M.ArchFn arch ids tp
                          -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp)))
     -- ^ Function for translating an architecture specific function
   , translateArchStmt :: !(M.ArchStmt arch ids -> CrucGen arch ids s ())
     -- ^ Function for translating an architecture specific statement.
   , handleAlloc :: !(C.HandleAllocator s)
     -- ^ Handle allocator
   , binaryPath :: !Text
     -- ^ Name of binary these blocks come from.
   , macawIndexToLabelMap :: !(Map Word64 (C.Label s))
     -- ^ Map from block indices to the associated label.
   , memSegmentMap :: !(Map M.SegmentIndex (C.Atom s (C.BVType (M.ArchAddrWidth arch))))
     -- ^ Map from segment indices to the Crucible value denoting the base.
   , regValueMap :: !(MapF (M.ArchReg arch) (WrappedAtom s))
     -- ^ Maps Macaw register initial values in block to associated Crucible value.
   , syscallHandle :: C.FnHandle (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch)
     -- ^ Function to call for system call
   }

type CrucSeenBlockMap s arch = Map Word64 (C.Block s (MacawFunctionResult arch))

-- | State that needs to be persisted across block translations
data CrucPersistentState arch ids s
   = CrucPersistentState
   { handleMap :: !(CrucGenHandles arch)
     -- ^ Handles found so far
   , valueCount :: !Int
     -- ^ Counter used to get fresh indices for Crucible atoms.
   , assignValueMap :: !(MapF (M.AssignId ids) (WrappedAtom s))
     -- ^ Map Macaw assign id to associated Crucible value.
   , seenBlockMap :: !(CrucSeenBlockMap s arch)
     -- ^ Map Macaw block indices to the associated crucible block
   }

handleMapLens :: Simple Lens (CrucPersistentState arch ids s) (CrucGenHandles arch)
handleMapLens = lens handleMap (\s v -> s { handleMap = v })

seenBlockMapLens :: Simple Lens (CrucPersistentState arch ids s) (CrucSeenBlockMap s arch)
seenBlockMapLens = lens seenBlockMap (\s v -> s { seenBlockMap = v })

-- | State used for generating blocks
data CrucGenState arch ids s
   = CrucGenState
   { crucCtx :: !(CrucGenContext arch ids s)
   , crucPState :: !(CrucPersistentState arch ids s)
   , blockLabel :: (C.Label s)
     -- ^ Label for this block we are translating
   , macawBlockIndex :: !Word64
   , codeAddr :: !Word64
     -- ^ Address of this code
   , prevStmts :: ![C.Posd (C.Stmt s)]
     -- ^ List of states in reverse order
   }

crucPStateLens :: Simple Lens (CrucGenState arch ids s) (CrucPersistentState arch ids s)
crucPStateLens = lens crucPState (\s v -> s { crucPState = v })

assignValueMapLens :: Simple Lens (CrucGenState arch ids s) (MapF (M.AssignId ids) (WrappedAtom s))
assignValueMapLens = crucPStateLens . lens assignValueMap (\s v -> s { assignValueMap = v })

newtype CrucGen arch ids s r
   = CrucGen { unContGen
               :: CrucGenState arch ids s
                  -> (CrucGenState arch ids s -> r -> ST s (CrucPersistentState arch ids s))
                  -> ST s (CrucPersistentState arch ids s)
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

getCtx :: CrucGen arch ids s (CrucGenContext arch ids s)
getCtx = gets crucCtx

liftST :: ST s r -> CrucGen arch ids s r
liftST m = CrucGen $ \s cont -> m >>= cont s

getPos :: CrucGen arch ids s C.Position
getPos = C.BinaryPos <$> (binaryPath <$> getCtx) <*> gets codeAddr

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
  pure $!  crucPState s & seenBlockMapLens %~ Map.insert (macawBlockIndex s) blk

freshValueIndex :: CrucGen arch ids s Int
freshValueIndex = do
  s <- get
  let ps = crucPState s
  let cnt = valueCount ps
  put $! s { crucPState = ps { valueCount = cnt + 1 } }
  pure $! cnt

-- | Evaluate the crucible app and return a reference to the result.
evalAtom :: C.AtomValue s ctp -> CrucGen arch ids s (C.Atom s ctp)
evalAtom av = do
  fname <- binaryPath <$> getCtx
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
  cns <- archConstraints <$> getCtx
  cns $ do
  case v of
    M.BVValue w c -> do
      crucibleValue (C.BVLit w c)
    M.BoolValue b -> do
      crucibleValue (C.BoolLit b)
    M.RelocatableValue w addr -> do
      case M.viewAddr addr of
        Left base -> do
          crucibleValue (C.BVLit w (toInteger base))
        Right (seg,off) -> do
          let idx = M.segmentIndex seg
          segMap <- memSegmentMap <$> getCtx
          case Map.lookup idx segMap of
            Just a -> do
              offset <- crucibleValue (C.BVLit w (toInteger off))
              crucibleValue (C.BVAdd w a offset)
            Nothing -> fail $ "internal: No Crucible address associated with segment."
    M.Initial r -> do
      regmap <- regValueMap <$> getCtx
      case MapF.lookup r regmap of
        Just (WrappedAtom a) -> pure a
        Nothing -> fail $ "internal: Register is not bound."
    M.AssignedValue asgn -> do
      let idx = M.assignId asgn
      amap <- use assignValueMapLens
      case MapF.lookup idx amap of
        Just (WrappedAtom r) -> pure r
        Nothing ->  fail "internal: Assignment id is not bound."

freshSymbolicHandle :: M.TypeRepr tp
                    -> CrucGen arch ids s (C.FnHandle EmptyCtx (ToCrucibleType tp))
freshSymbolicHandle repr = do
  hmap <- use $ crucPStateLens . handleMapLens . freshSymHandleMapLens
  case MapF.lookup repr hmap of
    Just (SymbolicHandle h) -> pure h
    Nothing -> do
      let fnm = case repr of
                  M.BoolTypeRepr -> "symbolicBool"
                  M.BVTypeRepr w -> fromString $ "symbolicBV" ++ show w
      halloc <- handleAlloc <$> getCtx
      hndl <- liftST $ C.mkHandle' halloc fnm Ctx.empty (typeToCrucible repr)
      crucPStateLens . handleMapLens . freshSymHandleMapLens %= MapF.insert repr (SymbolicHandle hndl)
      pure $! hndl

archWidthRepr :: forall arch ids s . CrucGenContext arch ids s -> NatRepr (M.ArchAddrWidth arch)
archWidthRepr ctx = archConstraints ctx $
  let arepr :: M.AddrWidthRepr (M.ArchAddrWidth arch)
      arepr = M.addrWidthRepr arepr
   in M.addrWidthNatRepr arepr

readMemHandle :: M.MemRepr tp
              -> CrucGen arch ids s (ReadMemHandle arch (ToCrucibleType tp))
readMemHandle repr = do
  hmap <- use $ crucPStateLens . handleMapLens . readMemHandleMapLens
  case MapF.lookup repr hmap of
    Just (SymbolicHandle r) -> pure r
    Nothing -> do
      cns <- archConstraints <$> getCtx
      cns $ do
      halloc <- handleAlloc <$> getCtx
      let fnm = case repr of
                  M.BVMemRepr w _ -> fromString $ "readWord" ++ show (8 * natValue w)
      wrepr <- archWidthRepr <$> getCtx
      let argTypes = Ctx.empty Ctx.%> C.BVRepr wrepr
      hndl <- liftST $ C.mkHandle' halloc fnm argTypes (memReprToCrucible repr)
      crucPStateLens . handleMapLens . readMemHandleMapLens %= MapF.insert repr (SymbolicHandle hndl)
      pure hndl

writeMemHandle :: M.MemRepr tp
               -> CrucGen arch ids s (WriteMemHandle arch (ToCrucibleType tp))
writeMemHandle repr = do
  hmap <- use $ crucPStateLens . handleMapLens . writeMemHandleMapLens
  case MapF.lookup repr hmap of
    Just (WriteMemWrapper r) -> pure r
    Nothing -> do
      cns <- archConstraints <$> getCtx
      cns $ do
      halloc <- handleAlloc <$> getCtx
      let fnm = case repr of
                  M.BVMemRepr w _ -> fromString $ "readWord" ++ show (8 * natValue w)
      wrepr <- archWidthRepr <$> getCtx
      let argTypes = Ctx.empty Ctx.%> C.BVRepr wrepr Ctx.%> memReprToCrucible repr
      hndl <- liftST $ C.mkHandle' halloc fnm argTypes C.UnitRepr
      crucPStateLens . handleMapLens . writeMemHandleMapLens %= MapF.insert repr (WriteMemWrapper hndl)
      pure hndl

-- | Call a function handle
callFnHandle :: C.FnHandle args ret
                -- ^ Handle to call
             -> Ctx.Assignment (C.Atom s) args
                -- ^ Arguments to function
             -> CrucGen arch ids s (C.Atom s ret)
callFnHandle hndl args = do
  hatom <- crucibleValue (C.HandleLit hndl)
  evalAtom $ C.Call hatom args (C.handleReturnType hndl)

-- | Create a fresh symbolic value of the given type.
freshSymbolic :: M.TypeRepr tp -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
freshSymbolic repr = do
  hndl <- freshSymbolicHandle repr
  callFnHandle hndl Ctx.empty

-- | Read the given memory address
readMem :: M.ArchAddrValue arch ids
        -> M.MemRepr tp
        -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
readMem addr repr = do
  hndl <- readMemHandle repr
  caddr <- valueToCrucible addr
  callFnHandle hndl (Ctx.empty Ctx.%> caddr)

writeMem :: M.ArchAddrValue arch ids
        -> M.MemRepr tp
        -> M.Value arch ids tp
        -> CrucGen arch ids s ()
writeMem addr repr val = do
  hndl <- writeMemHandle repr
  caddr <- valueToCrucible addr
  cval  <- valueToCrucible val
  let args = Ctx.empty Ctx.%> caddr Ctx.%> cval
  void $ callFnHandle hndl args

assignRhsToCrucible :: M.AssignRhs arch ids tp
                    -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
assignRhsToCrucible rhs =
  case rhs of
    M.EvalApp app -> appToCrucible app
    M.SetUndefined mrepr -> freshSymbolic mrepr
    M.ReadMem addr repr -> readMem addr repr
    M.EvalArchFn f _ -> do
      fn <- translateArchFn <$> getCtx
      fn f

addMacawStmt :: M.Stmt arch ids -> CrucGen arch ids s ()
addMacawStmt stmt =
  case stmt of
    M.AssignStmt asgn -> do
      let idx = M.assignId asgn
      a <- assignRhsToCrucible (M.assignRhs asgn)
      assignValueMapLens %= MapF.insert idx (WrappedAtom a)
    M.WriteMem addr repr val -> do
      writeMem addr repr val
    M.PlaceHolderStmt _vals msg -> do
      cmsg <- crucibleValue (C.TextLit (Text.pack msg))
      addTermStmt (C.ErrorStmt cmsg)
    M.InstructionStart addr _ -> do
      cns <- archConstraints <$> getCtx
      cns $ do
      modify $ \s -> s { codeAddr = fromIntegral addr }
    M.Comment _txt -> do
      pure ()
    M.ExecArchStmt astmt -> do
      f <- translateArchStmt <$> getCtx
      f astmt

lookupCrucibleLabel :: Word64 -> CrucGen arch ids s (C.Label s)
lookupCrucibleLabel idx = do
  m <- macawIndexToLabelMap <$> getCtx
  case Map.lookup idx m of
    Nothing -> fail $ "Could not find label for block " ++ show idx
    Just l -> pure l

createRegStruct :: M.RegState (M.ArchReg arch) (M.Value arch ids)
                -> CrucGen arch ids s (C.Atom s (ArchRegStruct arch))
createRegStruct _regs = do
  let ctx = undefined
      a = undefined
  crucibleValue (C.MkStruct ctx a)

addMacawTermStmt :: M.TermStmt arch ids -> CrucGen arch ids s ()
addMacawTermStmt tstmt =
  case tstmt of
    M.FetchAndExecute regs -> do
      s <- createRegStruct regs
      addTermStmt (C.Return s)
    M.Branch macawPred macawTrueLbl macawFalseLbl -> do
      p <- valueToCrucible macawPred
      t <- lookupCrucibleLabel macawTrueLbl
      f <- lookupCrucibleLabel macawFalseLbl
      addTermStmt (C.Br p t f)
    M.Syscall regs -> do
      h <- syscallHandle <$> getCtx
      s  <- createRegStruct regs
      s' <- callFnHandle h (Ctx.empty Ctx.%> s)
      addTermStmt (C.Return s')
    M.TranslateError _regs msg -> do
      cmsg <- crucibleValue (C.TextLit msg)
      addTermStmt (C.ErrorStmt cmsg)

addMacawBlock :: CrucGenContext arch ids s
                -> Word64 -- ^ Starting IP for block
                -> M.Block arch ids
                -> ExceptT String
                           (StateT (CrucPersistentState arch ids s) (ST s))
                           ()
addMacawBlock ctx addr b = do
  pstate <- get
  let idx = M.blockLabel b
  lbl <-
    case Map.lookup idx (macawIndexToLabelMap ctx) of
      Just lbl -> pure lbl
      Nothing -> throwError $ "Internal: Could not find block with index " ++ show idx
  let s0 = CrucGenState { crucCtx = ctx
                        , crucPState = pstate
                        , blockLabel = lbl
                        , macawBlockIndex = idx
                        , codeAddr = addr
                        , prevStmts = []
                        }
  let cont _s () = fail "Unterminated crucible block"
  let action = do
        mapM_ addMacawStmt (M.blockStmts b)
        addMacawTermStmt (M.blockTerm b)
  r <- lift $ lift $ unContGen action s0 cont
  put $!r
