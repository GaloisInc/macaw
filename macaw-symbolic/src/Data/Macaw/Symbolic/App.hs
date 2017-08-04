{-
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
module Data.Macaw.Symbolic.App
  ( UsedHandleSet
  , IndexPair(..)
  , CrucGenContext(..)
  , archWidthRepr
  , RegIndexMap
  , mkRegIndexMap
  , ArchAddrCrucibleType
  , ArchRegStruct
  , MemSegmentMap
  , HandleId(..)
  , handleIdName
  , handleIdRetType
  , HandleVal(..)
  , CrucPersistentState(..)
  , initCrucPersistentState
  , CrucGen
  , ToCrucibleType
  , CrucSeenBlockMap
  , CtxToCrucibleType
  , macawAssignToCruc
  , macawAssignToCrucM
  , ArchRegContext
  , ArchCrucibleRegTypes
  , MacawFunctionArgs
  , MacawFunctionResult
  , typeToCrucible
  , typeCtxToCrucible
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
import           Data.Maybe
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.FunctionName as C
import           Lang.Crucible.ProgramLoc as C
import qualified Lang.Crucible.Types as C

type family ToCrucibleBaseType (mtp :: M.Type) :: C.BaseType where
  ToCrucibleBaseType (M.BVType w) = C.BaseBVType w
  ToCrucibleBaseType M.BoolType   = C.BaseBoolType


type ToCrucibleType tp = C.BaseToType (ToCrucibleBaseType tp)

type family CtxToCrucibleType (mtp :: Ctx M.Type) :: Ctx C.CrucibleType where
  CtxToCrucibleType EmptyCtx   = EmptyCtx
  CtxToCrucibleType (c ::> tp) = CtxToCrucibleType c ::> ToCrucibleType tp

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

-- | Type family for arm registers
type family ArchRegContext (arch :: *) :: Ctx M.Type

-- | List of crucible types for architecture.
type ArchCrucibleRegTypes (arch :: *) = CtxToCrucibleType (ArchRegContext arch)

type ArchRegStruct (arch :: *) = C.StructType (ArchCrucibleRegTypes arch)
type MacawFunctionArgs arch = EmptyCtx ::> ArchRegStruct arch
type MacawFunctionResult arch = ArchRegStruct arch

typeToCrucibleBase :: M.TypeRepr tp -> C.BaseTypeRepr (ToCrucibleBaseType tp)
typeToCrucibleBase tp =
  case tp of
    M.BoolTypeRepr -> C.BaseBoolRepr
    M.BVTypeRepr w -> C.BaseBVRepr w

typeToCrucible :: M.TypeRepr tp -> C.TypeRepr (ToCrucibleType tp)
typeToCrucible = C.baseToType . typeToCrucibleBase

-- Return the types associated with a register assignment.
typeCtxToCrucible :: Ctx.Assignment M.TypeRepr ctx
                  -> Ctx.Assignment C.TypeRepr (CtxToCrucibleType ctx)
typeCtxToCrucible = macawAssignToCruc typeToCrucible

memReprToCrucible :: M.MemRepr tp -> C.TypeRepr (ToCrucibleType tp)
memReprToCrucible = typeToCrucible . M.typeRepr

-- | A Crucible value with a Macaw type.
data MacawCrucibleValue f tp = MacawCrucibleValue (f (ToCrucibleType tp))

type ArchConstraints arch
   = ( M.MemWidth (M.ArchAddrWidth arch)
     , OrdF (M.ArchReg arch)
     , M.HasRepr (M.ArchReg arch) M.TypeRepr
     )

type ArchAddrCrucibleType arch = C.BVType (M.ArchAddrWidth arch)

data HandleVal (ftp :: (Ctx C.CrucibleType, C.CrucibleType)) =
  forall args res . (ftp ~ '(args, res)) => HandleVal !(C.FnHandle args res)

-- | This  getting information about what handles are used
type UsedHandleSet arch = MapF (HandleId arch) HandleVal

-- | Map from indices of segments without a fixed base address to a
-- global variable storing the base address.
type MemSegmentMap w = Map M.SegmentIndex (C.GlobalVar (C.BVType w))

data IndexPair ctx tp = IndexPair { macawIndex    :: !(Ctx.Index ctx tp)
                                  , crucibleIndex :: !(Ctx.Index (CtxToCrucibleType ctx) (ToCrucibleType tp))
                                  }

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

data CrucGenContext arch ids s
   = CrucGenContext
   { archConstraints :: !(forall a . (ArchConstraints arch => a) -> a)
     -- ^ Typeclass constraints for architecture
   , macawRegAssign :: !(Ctx.Assignment (M.ArchReg arch) (ArchRegContext arch))
     -- ^ Assignment from register to the context
   , regIndexMap :: !(RegIndexMap arch)
     -- ^ Maps Macaw registers to the associated index.
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
   , memSegmentMap :: !(MemSegmentMap (M.ArchAddrWidth arch))
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
-- Handles

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

------------------------------------------------------------------------
-- CrucPersistentState

type CrucSeenBlockMap s arch = Map Word64 (C.Block s (MacawFunctionResult arch))

-- | State that needs to be persisted across block translations
data CrucPersistentState arch ids s
   = CrucPersistentState
   { handleMap :: !(UsedHandleSet arch)
     -- ^ Handles found so far
   , valueCount :: !Int
     -- ^ Counter used to get fresh indices for Crucible atoms.
   , assignValueMap :: !(MapF (M.AssignId ids) (MacawCrucibleValue (C.Atom s)))
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

-- | State used for generating blocks
data CrucGenState arch ids s
   = CrucGenState
   { crucCtx :: !(CrucGenContext arch ids s)
   , crucPState :: !(CrucPersistentState arch ids s)
   , blockLabel :: (C.Label s)
     -- ^ Label for this block we are translating
   , macawBlockIndex :: !Word64
   , codeAddr :: !(M.ArchSegmentOff arch)
     -- ^ Address of this code
   , prevStmts :: ![C.Posd (C.Stmt s)]
     -- ^ List of states in reverse order
   }

crucPStateLens :: Simple Lens (CrucGenState arch ids s) (CrucPersistentState arch ids s)
crucPStateLens = lens crucPState (\s v -> s { crucPState = v })

assignValueMapLens :: Simple Lens (CrucGenState arch ids s)
                                  (MapF (M.AssignId ids) (MacawCrucibleValue (C.Atom s)))
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

-- | Get current position
getPos :: CrucGen arch ids s C.Position
getPos = do
  ctx <- getCtx
  archConstraints ctx $ do
  a <- gets codeAddr
  let absAddr = fromMaybe (M.msegOffset a) (M.msegAddr a)
  pure $ C.BinaryPos (binaryPath ctx) (fromIntegral absAddr)

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
  p <- getPos
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

-- | Evaluate the crucible app and return a reference to the result.
getRegInput :: IndexPair (ArchRegContext arch) tp -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
getRegInput idx = do
  ctx <- getCtx
  archConstraints ctx $ do
  -- Make atom
  let regStruct = C.Atom { C.atomPosition = C.InternalPos
                         , C.atomId = 0
                         , C.atomSource = C.FnInput
                         , C.typeOfAtom = regStructRepr ctx
                         }
  let tp = M.typeRepr (macawRegAssign ctx Ctx.! macawIndex idx)
  crucibleValue (C.GetStruct regStruct (crucibleIndex idx) (typeToCrucible tp))

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
          when (isJust (M.segmentBase seg)) $ do
            fail "internal: Expected segment without fixed base"

          let idx = M.segmentIndex seg
          segMap <- memSegmentMap <$> getCtx
          case Map.lookup idx segMap of
            Just g -> do
              a <- evalAtom (C.ReadGlobal g)
              offset <- crucibleValue (C.BVLit w (toInteger off))
              crucibleValue (C.BVAdd w a offset)
            Nothing ->
              fail $ "internal: No Crucible address associated with segment."
    M.Initial r -> do
      regmap <- regIndexMap <$> getCtx
      case MapF.lookup r regmap of
        Just idx -> getRegInput idx
        Nothing -> fail $ "internal: Register is not bound."
    M.AssignedValue asgn -> do
      let idx = M.assignId asgn
      amap <- use assignValueMapLens
      case MapF.lookup idx amap of
        Just (MacawCrucibleValue r) -> pure r
        Nothing ->  fail "internal: Assignment id is not bound."

mkHandleVal :: HandleId arch '(args,ret)
            -> CrucGen arch ids s (C.FnHandle args ret)
mkHandleVal hid = do
  hmap <- use $ crucPStateLens . handleMapLens
  case MapF.lookup hid hmap of
    Just (HandleVal h) -> pure h
    Nothing -> do
      ctx <- getCtx
      let argTypes = handleIdArgTypes ctx hid
      let retType = handleIdRetType ctx hid
      hndl <- liftST $ C.mkHandle' (handleAlloc ctx) (handleIdName hid) argTypes retType
      crucPStateLens . handleMapLens %= MapF.insert hid (HandleVal hndl)
      pure $! hndl

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
  hndl <- mkHandleVal (MkFreshSymId repr)
  callFnHandle hndl Ctx.empty

-- | Read the given memory address
readMem :: M.ArchAddrValue arch ids
        -> M.MemRepr tp
        -> CrucGen arch ids s (C.Atom s (ToCrucibleType tp))
readMem addr repr = do
  hndl <- mkHandleVal (ReadMemId repr)
  caddr <- valueToCrucible addr
  callFnHandle hndl (Ctx.empty Ctx.%> caddr)

writeMem :: M.ArchAddrValue arch ids
        -> M.MemRepr tp
        -> M.Value arch ids tp
        -> CrucGen arch ids s ()
writeMem addr repr val = do
  hndl <- mkHandleVal (WriteMemId repr)
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
      assignValueMapLens %= MapF.insert idx (MacawCrucibleValue a)
    M.WriteMem addr repr val -> do
      writeMem addr repr val
    M.PlaceHolderStmt _vals msg -> do
      cmsg <- crucibleValue (C.TextLit (Text.pack msg))
      addTermStmt (C.ErrorStmt cmsg)
    M.InstructionStart _addr _ -> do
      -- TODO: Fix this
      pure ()
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

-- | Create a crucible struct for registers from a register state.
createRegStruct :: forall arch ids s
                .  M.RegState (M.ArchReg arch) (M.Value arch ids)
                -> CrucGen arch ids s (C.Atom s (ArchRegStruct arch))
createRegStruct regs = do
  ctx <- getCtx
  archConstraints ctx $ do
  let regAssign = macawRegAssign ctx
  let tps = fmapFC M.typeRepr regAssign
  let a = fmapFC (\r -> regs ^. M.boundValue r) regAssign
  fields <- macawAssignToCrucM valueToCrucible a
  crucibleValue $ C.MkStruct (typeCtxToCrucible tps) fields

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
      h <- mkHandleVal SyscallId
      s  <- createRegStruct regs
      s' <- callFnHandle h (Ctx.empty Ctx.%> s)
      addTermStmt (C.Return s')
    M.TranslateError _regs msg -> do
      cmsg <- crucibleValue (C.TextLit msg)
      addTermStmt (C.ErrorStmt cmsg)

type MacawMonad arch ids s = ExceptT String (StateT (CrucPersistentState arch ids s) (ST s))

addMacawBlock :: CrucGenContext arch ids s
              -> M.Block arch ids
              -> MacawMonad arch ids s ()
addMacawBlock ctx b = do
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
                        , codeAddr = M.blockAddr b
                        , prevStmts = []
                        }
  let cont _s () = fail "Unterminated crucible block"
  let action = do
        mapM_ addMacawStmt (M.blockStmts b)
        addMacawTermStmt (M.blockTerm b)
  r <- lift $ lift $ unContGen action s0 cont
  put r
