{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines the core operations for mapping from Reopt to Crucible.
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
  ( ArchTranslateFunctions(..)
  , MacawMonad
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
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableFC
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as Text
import           Data.Word
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.FunctionHandle as C
import           Lang.Crucible.ProgramLoc as C
import qualified Lang.Crucible.Solver.Symbol as C

import           Data.Macaw.Symbolic.PersistentState

------------------------------------------------------------------------
-- CrucPersistentState

-- | Architecture-specific information needed to translate from Macaw to Crucible
data ArchTranslateFunctions arch
  = ArchTranslateFunctions
  { archRegNameFn :: !(forall tp . M.ArchReg arch tp -> C.SolverSymbol)
  , archRegAssignment :: !(Ctx.Assignment (M.ArchReg arch) (ArchRegContext arch))
  , archTranslateFn :: !(forall ids s tp
                         . M.ArchFn arch (M.Value arch ids) tp
                         -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp)))
     -- ^ Function for translating an architecture specific function
  , archTranslateStmt :: !(forall ids s . M.ArchStmt arch ids -> CrucGen arch ids s ())
  , archTranslateTermStmt :: !(forall ids s
                               . M.ArchTermStmt arch ids
                               -> M.RegState (M.ArchReg arch) (M.Value arch ids)
                               -> CrucGen arch ids s ())
  }

-- | State used for generating blocks
data CrucGenState arch ids s
   = CrucGenState
   { translateFns :: !(ArchTranslateFunctions arch)
   , crucCtx :: !(CrucGenContext arch ids s)
   , crucPState :: !(CrucPersistentState arch ids s)
     -- ^ State that persists across blocks.
   , blockLabel :: (CR.Label s)
     -- ^ Label for this block we are translating
   , macawBlockIndex :: !Word64
   , codeAddr :: !(M.ArchSegmentOff arch)
     -- ^ Address of this code
   , prevStmts :: ![C.Posd (CR.Stmt s)]
     -- ^ List of states in reverse order
   }

crucPStateLens :: Simple Lens (CrucGenState arch ids s) (CrucPersistentState arch ids s)
crucPStateLens = lens crucPState (\s v -> s { crucPState = v })

assignValueMapLens :: Simple Lens (CrucGenState arch ids s)
                                  (MapF (M.AssignId ids) (MacawCrucibleValue (CR.Atom s)))
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

addStmt :: CR.Stmt s -> CrucGen arch ids s ()
addStmt stmt = seq stmt $ do
  p <- getPos
  s <- get
  let pstmt = C.Posd p stmt
  seq pstmt $ do
  put $! s { prevStmts = pstmt : prevStmts s }

addTermStmt :: CR.TermStmt s (MacawFunctionResult arch)
            -> CrucGen arch ids s a
addTermStmt tstmt = do
  termPos <- getPos
  CrucGen $ \s _ -> do
  let lbl = CR.LabelID (blockLabel s)
  let stmts = Seq.fromList (reverse (prevStmts s))
  let term = C.Posd termPos tstmt
  let blk = CR.mkBlock lbl Set.empty stmts term
  pure $!  crucPState s & seenBlockMapLens %~ Map.insert (macawBlockIndex s) blk

freshValueIndex :: CrucGen arch ids s Int
freshValueIndex = do
  s <- get
  let ps = crucPState s
  let cnt = valueCount ps
  put $! s { crucPState = ps { valueCount = cnt + 1 } }
  pure $! cnt

-- | Evaluate the crucible app and return a reference to the result.
evalAtom :: CR.AtomValue s ctp -> CrucGen arch ids s (CR.Atom s ctp)
evalAtom av = do
  p <- getPos
  i <- freshValueIndex
  -- Make atom
  let atom = CR.Atom { CR.atomPosition = p
                     , CR.atomId = i
                     , CR.atomSource = CR.Assigned
                     , CR.typeOfAtom = CR.typeOfAtomValue av
                     }
  addStmt $ CR.DefineAtom atom av
  pure $! atom

-- | Evaluate the crucible app and return a reference to the result.
crucibleValue :: C.App (CR.Atom s) ctp -> CrucGen arch ids s (CR.Atom s ctp)
crucibleValue app = evalAtom (CR.EvalApp app)

-- | Evaluate the crucible app and return a reference to the result.
getRegInput :: IndexPair (ArchRegContext arch) tp -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
getRegInput idx = do
  ctx <- getCtx
  archConstraints ctx $ do
  -- Make atom
  let regStruct = CR.Atom { CR.atomPosition = C.InternalPos
                          , CR.atomId = 0
                          , CR.atomSource = CR.FnInput
                          , CR.typeOfAtom = regStructRepr ctx
                          }
  let tp = M.typeRepr (macawRegAssign ctx Ctx.! macawIndex idx)
  crucibleValue (C.GetStruct regStruct (crucibleIndex idx) (typeToCrucible tp))

v2c :: M.Value arch ids tp
    -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
v2c = valueToCrucible

-- | Evaluate the crucible app and return a reference to the result.
appAtom :: C.App (CR.Atom s) ctp -> CrucGen arch ids s (CR.Atom s ctp)
appAtom app = evalAtom (CR.EvalApp app)

appToCrucible :: M.App (M.Value arch ids) tp
              -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
appToCrucible app = do
  ctx <- getCtx
  archConstraints ctx $ do
  case app of
    M.Mux M.BoolTypeRepr c t f ->
      appAtom =<< C.BoolIte <$> v2c c <*> v2c t <*> v2c f
    M.Mux (M.BVTypeRepr w) c t f ->
      appAtom =<< C.BVIte <$> v2c c <*> pure w <*> v2c t <*> v2c f
    M.Trunc x w -> appAtom =<< C.BVTrunc w (M.typeWidth x) <$> v2c x
    M.SExt x w  -> appAtom =<< C.BVSext  w (M.typeWidth x) <$> v2c x
    M.UExt x w  -> appAtom =<< C.BVZext  w (M.typeWidth x) <$> v2c x
    M.AndApp x y  -> appAtom =<< C.And     <$> v2c x <*> v2c y
    M.OrApp  x y  -> appAtom =<< C.Or      <$> v2c x <*> v2c y
    M.NotApp x    -> appAtom =<< C.Not     <$> v2c x
    M.XorApp x y  -> appAtom =<< C.BoolXor <$> v2c x <*> v2c y
    M.BVAdd w x y -> appAtom =<< C.BVAdd w <$> v2c x <*> v2c y
    M.BVSub w x y -> appAtom =<< C.BVSub w <$> v2c x <*> v2c y
    M.BVMul w x y -> appAtom =<< C.BVMul w <$> v2c x <*> v2c y

valueToCrucible :: M.Value arch ids tp
                -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
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
              a <- evalAtom (CR.ReadGlobal g)
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
             -> Ctx.Assignment (CR.Atom s) args
                -- ^ Arguments to function
             -> CrucGen arch ids s (CR.Atom s ret)
callFnHandle hndl args = do
  hatom <- crucibleValue (C.HandleLit hndl)
  evalAtom $ CR.Call hatom args (C.handleReturnType hndl)

-- | Create a fresh symbolic value of the given type.
freshSymbolic :: M.TypeRepr tp
              -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
freshSymbolic repr = do
  hndl <- mkHandleVal (MkFreshSymId repr)
  callFnHandle hndl Ctx.empty

-- | Read the given memory address
readMem :: M.ArchAddrValue arch ids
        -> M.MemRepr tp
        -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
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
                    -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
assignRhsToCrucible rhs =
  case rhs of
    M.EvalApp app -> appToCrucible app
    M.SetUndefined mrepr -> freshSymbolic mrepr
    M.ReadMem addr repr -> readMem addr repr
    M.EvalArchFn f _ -> do
      fns <- translateFns <$> get
      archTranslateFn fns f

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
      addTermStmt (CR.ErrorStmt cmsg)
    M.InstructionStart _addr _ -> do
      -- TODO: Fix this
      pure ()
    M.Comment _txt -> do
      pure ()
    M.ExecArchStmt astmt -> do
      fns <- translateFns <$> get
      archTranslateStmt fns astmt

lookupCrucibleLabel :: Word64 -> CrucGen arch ids s (CR.Label s)
lookupCrucibleLabel idx = do
  m <- macawIndexToLabelMap <$> getCtx
  case Map.lookup idx m of
    Nothing -> fail $ "Could not find label for block " ++ show idx
    Just l -> pure l

-- | Create a crucible struct for registers from a register state.
createRegStruct :: forall arch ids s
                .  M.RegState (M.ArchReg arch) (M.Value arch ids)
                -> CrucGen arch ids s (CR.Atom s (ArchRegStruct arch))
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
      addTermStmt (CR.Return s)
    M.Branch macawPred macawTrueLbl macawFalseLbl -> do
      p <- valueToCrucible macawPred
      t <- lookupCrucibleLabel macawTrueLbl
      f <- lookupCrucibleLabel macawFalseLbl
      addTermStmt (CR.Br p t f)
    M.ArchTermStmt ts regs -> do
      fns <- translateFns <$> get
      archTranslateTermStmt fns ts regs
--    M.Syscall regs -> do
--      h <- mkHandleVal SyscallId
--      s  <- createRegStruct regs
--      s' <- callFnHandle h (Ctx.empty Ctx.%> s)
--      addTermStmt (C.Return s')
    M.TranslateError _regs msg -> do
      cmsg <- crucibleValue (C.TextLit msg)
      addTermStmt (CR.ErrorStmt cmsg)

-- | Type level monad for building blocks.
type MacawMonad arch ids s = ExceptT String (StateT (CrucPersistentState arch ids s) (ST s))

addMacawBlock :: ArchTranslateFunctions arch
              -> CrucGenContext arch ids s
              -> M.Block arch ids
              -> MacawMonad arch ids s ()
addMacawBlock tfns ctx b = do
  pstate <- get
  let idx = M.blockLabel b
  lbl <-
    case Map.lookup idx (macawIndexToLabelMap ctx) of
      Just lbl -> pure lbl
      Nothing -> throwError $ "Internal: Could not find block with index " ++ show idx
  let s0 = CrucGenState { translateFns = tfns
                        , crucCtx = ctx
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
