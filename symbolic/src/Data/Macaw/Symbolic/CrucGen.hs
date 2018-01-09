{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines the core operations for mapping from Reopt to Crucible.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.Symbolic.CrucGen
  ( CrucGenArchFunctions(..)
  , MacawExt
  , MacawStmtExtension(..)
    -- ** Operations for implementing new backends.
  , CrucGen
  , MacawMonad
  , runMacawMonad
  , addMacawBlock
  , addParsedBlock
  , nextStatements
  ) where

import           Control.Lens hiding (Empty, (:>))
import           Control.Monad.Except
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Bits
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.CFG.Block as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Memory as M
import qualified Data.Macaw.Types as M
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as Text
import           Data.Word
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as CR
import           Lang.Crucible.ProgramLoc as C
import qualified Lang.Crucible.Solver.Symbol as C
import qualified Lang.Crucible.Types as C
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.Symbolic.PersistentState

------------------------------------------------------------------------
-- CrucPersistentState

-- | Architecture-specific information needed to translate from Macaw to Crucible
data CrucGenArchFunctions arch
  = CrucGenArchFunctions
  { crucGenArchConstraints :: !(forall a . (M.MemWidth (M.ArchAddrWidth arch) => a) -> a)
  , crucGenRegAssignment :: !(Ctx.Assignment (M.ArchReg arch) (ArchRegContext arch))
    -- ^ Map from indices in the ArchRegContext to the associated register.
  , crucGenArchRegName :: !(forall tp . M.ArchReg arch tp -> C.SolverSymbol)
    -- ^ Provides a solver name to use for referring to register.
  , crucGenArchFn :: !(forall ids s tp
                         . M.ArchFn arch (M.Value arch ids) tp
                         -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp)))
     -- ^ Generate crucible for architecture-specific function.
  , crucGenArchStmt
    :: !(forall ids s . M.ArchStmt arch (M.Value arch ids) -> CrucGen arch ids s ())
     -- ^ Generate crucible for architecture-specific statement.
  , crucGenArchTermStmt :: !(forall ids s
                               . M.ArchTermStmt arch ids
                               -> M.RegState (M.ArchReg arch) (M.Value arch ids)
                               -> CrucGen arch ids s ())
     -- ^ Generate crucible for architecture-specific terminal statement.
  }

------------------------------------------------------------------------
-- MacawStmtExtension

data MacawStmtExtension (arch :: *) (f :: C.CrucibleType -> *) (tp :: C.CrucibleType) where
  MacawReadMem :: !(M.MemRepr tp)
               -> !(f (ArchAddrCrucibleType arch))
               -> MacawStmtExtension arch f (ToCrucibleType tp)
  MacawWriteMem :: !(M.MemRepr tp)
               -> !(f (ArchAddrCrucibleType arch))
               -> !(f (ToCrucibleType tp))
               -> MacawStmtExtension arch f C.UnitType
  MacawFreshSymbolic :: !(M.TypeRepr tp)
                     -> MacawStmtExtension arch f (ToCrucibleType tp)

instance FunctorFC (MacawStmtExtension arch) where
  fmapFC = fmapFCDefault

instance FoldableFC (MacawStmtExtension arch) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (MacawStmtExtension arch) where
  traverseFC f a0 =
    case a0 of
      MacawReadMem  r a   -> MacawReadMem r <$> f a
      MacawWriteMem r a v -> MacawWriteMem r <$> f a <*> f v
      MacawFreshSymbolic r -> pure (MacawFreshSymbolic r)

sexpr :: String -> [Doc] -> Doc
sexpr s [] = text s
sexpr s l  = parens (text s <+> hsep l)

instance C.PrettyApp (MacawStmtExtension arch) where
  ppApp f a0 =
    case a0 of
      MacawReadMem r a     -> sexpr "macawReadMem"  [pretty r, f a]
      MacawWriteMem r a v  -> sexpr "macawWriteMem" [pretty r, f a, f v]
      MacawFreshSymbolic r -> sexpr "macawFreshSymbolic" [ text (show r) ]

instance C.TypeApp (MacawStmtExtension arch) where
  appType (MacawReadMem r _) = memReprToCrucible r
  appType (MacawWriteMem _ _ _) = C.knownRepr
  appType (MacawFreshSymbolic r) = typeToCrucible r

------------------------------------------------------------------------
-- MacawExt

data MacawExt (arch :: *)

type instance C.ExprExtension (MacawExt arch) = C.EmptyExprExtension
type instance C.StmtExtension (MacawExt arch) = MacawStmtExtension arch

instance C.IsSyntaxExtension (MacawExt arch)

-- | State used for generating blocks
data CrucGenState arch ids s
   = CrucGenState
   { translateFns :: !(CrucGenArchFunctions arch)
   , crucCtx :: !(CrucGenContext arch s)
   , crucPState :: !(CrucPersistentState ids s)
     -- ^ State that persists across blocks.
   , macawPositionFn :: !(M.ArchAddrWord arch -> C.Position)
     -- ^ Map from offset to Crucible position.
   , blockLabel :: (CR.Label s)
     -- ^ Label for this block we are translating
   , codeOff :: !(M.ArchAddrWord arch)
     -- ^ Offset
   , prevStmts :: ![C.Posd (CR.Stmt (MacawExt arch) s)]
     -- ^ List of states in reverse order
   }

crucPStateLens :: Simple Lens (CrucGenState arch ids s) (CrucPersistentState ids s)
crucPStateLens = lens crucPState (\s v -> s { crucPState = v })

assignValueMapLens :: Simple Lens (CrucPersistentState ids s)
                                  (MapF (M.AssignId ids) (MacawCrucibleValue (CR.Atom s)))
assignValueMapLens = lens assignValueMap (\s v -> s { assignValueMap = v })

type CrucGenRet arch ids s = (CrucGenState arch ids s, CR.TermStmt s (MacawFunctionResult arch))

newtype CrucGen arch ids s r
   = CrucGen { unCrucGen
               :: CrucGenState arch ids s
                  -> (CrucGenState arch ids s
                      -> r
                      -> ST s (CrucGenRet arch ids s))
                  -> ST s (CrucGenRet arch ids s)
             }

instance Functor (CrucGen arch ids s) where
  fmap f m = CrucGen $ \s0 cont -> unCrucGen m s0 $ \s1 v -> cont s1 (f v)

instance Applicative (CrucGen arch ids s) where
  pure r = CrucGen $ \s cont -> cont s r
  mf <*> ma = CrucGen $ \s0 cont -> unCrucGen mf s0
                      $ \s1 f -> unCrucGen ma s1
                      $ \s2 a -> cont s2 (f a)

instance Monad (CrucGen arch ids s) where
  m >>= h = CrucGen $ \s0 cont -> unCrucGen m s0 $ \s1 r -> unCrucGen (h r) s1 cont

instance MonadState (CrucGenState arch ids s) (CrucGen arch ids s) where
  get = CrucGen $ \s cont -> cont s s
  put s = CrucGen $ \_ cont -> cont s ()

getCtx :: CrucGen arch ids s (CrucGenContext arch s)
getCtx = gets crucCtx

-- | Get current position
getPos :: CrucGen arch ids s C.Position
getPos = gets $ \s -> macawPositionFn s (codeOff s)

addStmt :: CR.Stmt (MacawExt arch) s -> CrucGen arch ids s ()
addStmt stmt = seq stmt $ do
  p <- getPos
  s <- get
  let pstmt = C.Posd p stmt
  seq pstmt $ do
  put $! s { prevStmts = pstmt : prevStmts s }

addTermStmt :: CR.TermStmt s (MacawFunctionResult arch)
            -> CrucGen arch ids s a
addTermStmt tstmt = do
  CrucGen $ \s _ -> pure (s, tstmt)
{-
  let termPos = macawPositionFn s (codeOff s)
  let lbl = blockLabel s
  let stmts = Seq.fromList (reverse (prevStmts s))
  let term = C.Posd termPos tstmt
  let blk = CR.mkBlock (CR.LabelID lbl) Set.empty stmts term
  pure $ (crucPState s, blk)
-}

freshValueIndex :: CrucGen arch ids s Int
freshValueIndex = do
  s <- get
  let ps = crucPState s
  let cnt = valueCount ps
  put $! s { crucPState = ps { valueCount = cnt + 1 } }
  pure $! cnt

-- | Evaluate the crucible app and return a reference to the result.
evalAtom :: CR.AtomValue (MacawExt arch) s ctp -> CrucGen arch ids s (CR.Atom s ctp)
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
crucibleValue :: C.App (MacawExt arch) (CR.Atom s) ctp -> CrucGen arch ids s (CR.Atom s ctp)
crucibleValue app = evalAtom (CR.EvalApp app)

-- | Evaluate the crucible app and return a reference to the result.
getRegInput :: Ctx.Assignment (M.ArchReg arch) (ArchRegContext arch)
            -> IndexPair (ArchRegContext arch) tp
            -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
getRegInput regAssign idx = do
  ctx <- getCtx
  archConstraints ctx $ do
  -- Make atom
  let regStruct = CR.Atom { CR.atomPosition = C.InternalPos
                          , CR.atomId = 0
                          , CR.atomSource = CR.FnInput
                          , CR.typeOfAtom = regStructRepr ctx
                          }
  let tp = M.typeRepr (regAssign Ctx.! macawIndex idx)
  crucibleValue (C.GetStruct regStruct (crucibleIndex idx) (typeToCrucible tp))

v2c :: M.Value arch ids tp
    -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
v2c = valueToCrucible

-- | Evaluate the crucible app and return a reference to the result.
appAtom :: C.App (MacawExt arch) (CR.Atom s) ctp -> CrucGen arch ids s (CR.Atom s ctp)
appAtom app = evalAtom (CR.EvalApp app)

-- | Create a crucible value for a bitvector literal.
bvLit :: (1 <= w) => NatRepr w -> Integer -> CrucGen arch ids s (CR.Atom s (C.BVType w))
bvLit w i = crucibleValue (C.BVLit w (i .&. maxUnsigned w))

incNatIsPos :: forall p w . p w -> LeqProof 1 (w+1)
incNatIsPos _ = leqAdd2 (LeqProof :: LeqProof 0 w) (LeqProof :: LeqProof 1 1)

zext1 :: forall arch ids s w
      .  (1 <= w)
      => NatRepr w
      -> CR.Atom s (C.BVType w)
      -> CrucGen arch ids s (CR.Atom s (C.BVType (w+1)))
zext1 w =
  case incNatIsPos w of
    LeqProof -> appAtom . C.BVZext (incNat w) w

msb :: (1 <= w) => NatRepr w -> CR.Atom s (C.BVType w) -> CrucGen arch ids s (CR.Atom s C.BoolType)
msb w x = do
  mask <- bvLit w (maxSigned w + 1)
  x_mask <- appAtom $ C.BVAnd w x mask
  appAtom (C.BVEq w x_mask mask)

bvAdc :: (1 <= w)
      => NatRepr w
      -> CR.Atom s (C.BVType w)
      -> CR.Atom s (C.BVType w)
      -> CR.Atom s C.BoolType
      -> CrucGen arch ids s (CR.Atom s (C.BVType w))
bvAdc w x y c = do
  s  <- appAtom $ C.BVAdd w x y
  cbv <- appAtom =<< C.BVIte c w <$> bvLit w 1 <*> bvLit w 0
  appAtom $ C.BVAdd w s cbv

appToCrucible :: M.App (M.Value arch ids) tp
              -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
appToCrucible app = do
  ctx <- getCtx
  archConstraints ctx $ do
  case app of
    M.Eq x y -> do
      let btp = typeToCrucibleBase (M.typeRepr x)
      appAtom =<< C.BaseIsEq btp <$> v2c x <*> v2c y
    M.Mux tp c t f -> do
      let btp = typeToCrucibleBase tp
      appAtom =<< C.BaseIte btp <$> v2c c <*> v2c t <*> v2c f
    M.TupleField tps x i ->
      undefined tps x i -- TODO: Fix this

    -- Booleans

    M.AndApp x y  -> appAtom =<< C.And     <$> v2c x <*> v2c y
    M.OrApp  x y  -> appAtom =<< C.Or      <$> v2c x <*> v2c y
    M.NotApp x    -> appAtom =<< C.Not     <$> v2c x
    M.XorApp x y  -> appAtom =<< C.BoolXor <$> v2c x <*> v2c y

    -- Extension operations
    M.Trunc x w -> appAtom =<< C.BVTrunc w (M.typeWidth x) <$> v2c x
    M.SExt x w  -> appAtom =<< C.BVSext  w (M.typeWidth x) <$> v2c x
    M.UExt x w  -> appAtom =<< C.BVZext  w (M.typeWidth x) <$> v2c x

    -- Bitvector arithmetic
    M.BVAdd w x y -> appAtom =<< C.BVAdd w <$> v2c x <*> v2c y
    M.BVAdc w x y c -> undefined w x y c
    M.BVSub w x y -> appAtom =<< C.BVSub w <$> v2c x <*> v2c y
    M.BVSbb w x y c -> undefined w x y c
    M.BVMul w x y -> appAtom =<< C.BVMul w <$> v2c x <*> v2c y
    M.BVUnsignedLe x y -> appAtom =<< C.BVUle (M.typeWidth x) <$> v2c x <*> v2c y
    M.BVUnsignedLt x y -> appAtom =<< C.BVUlt (M.typeWidth x) <$> v2c x <*> v2c y
    M.BVSignedLe   x y -> appAtom =<< C.BVSle (M.typeWidth x) <$> v2c x <*> v2c y
    M.BVSignedLt   x y -> appAtom =<< C.BVSlt (M.typeWidth x) <$> v2c x <*> v2c y

    -- Bitwise operations
    M.BVTestBit x i -> do
      let w = M.typeWidth x
      one <- bvLit w 1
      -- Create mask for ith index
      i_mask <- appAtom =<< C.BVShl w one <$> v2c i
      -- Mask off index
      x_mask <- appAtom =<< C.BVAnd w <$> v2c x <*> pure i_mask
      -- Check to see if result is i_mask
      appAtom (C.BVEq w x_mask i_mask)
    M.BVComplement w x -> appAtom =<< C.BVNot w <$> v2c x
    M.BVAnd w x y -> appAtom =<< C.BVAnd w <$> v2c x <*> v2c y
    M.BVOr  w x y -> appAtom =<< C.BVOr  w <$> v2c x <*> v2c y
    M.BVXor w x y -> appAtom =<< C.BVXor w <$> v2c x <*> v2c y
    M.BVShl w x y -> appAtom =<< C.BVShl  w <$> v2c x <*> v2c y
    M.BVShr w x y -> appAtom =<< C.BVLshr w <$> v2c x <*> v2c y
    M.BVSar w x y -> appAtom =<< C.BVAshr w <$> v2c x <*> v2c y

    M.UadcOverflows x y c -> do
      let w  = M.typeWidth x
      let w' = incNat w
      x' <- zext1 w =<< v2c x
      y' <- zext1 w =<< v2c y
      LeqProof <- pure (incNatIsPos w)
      r <- bvAdc w' x' y' =<< v2c c
      msb w' r
    M.SadcOverflows x y c -> do
      undefined x y c
    M.UsbbOverflows x y b -> do
      undefined x y b
    M.SsbbOverflows x y b -> do
      undefined x y b
    M.PopCount w x -> do
      undefined w x
    M.ReverseBytes w x -> do
      undefined w x
    M.Bsf w x -> do
      undefined w x
    M.Bsr w x -> do
      undefined w x

valueToCrucible :: M.Value arch ids tp
                -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
valueToCrucible v = do
 ctx <- getCtx
 archConstraints ctx $ do
  case v of
    M.BVValue w c -> bvLit w c
    M.BoolValue b -> crucibleValue (C.BoolLit b)
    -- In this case,
    M.RelocatableValue w addr
      | M.addrBase addr == 0 ->
        crucibleValue (C.BVLit w (toInteger (M.addrOffset addr)))
      | otherwise -> do
          let idx = M.addrBase addr
          segMap <- memBaseAddrMap <$> getCtx
          case Map.lookup idx segMap of
            Just g -> do
              a <- evalAtom (CR.ReadGlobal g)
              offset <- crucibleValue (C.BVLit w (toInteger (M.addrOffset addr)))
              crucibleValue (C.BVAdd w a offset)
            Nothing ->
              fail $ "internal: No Crucible address associated with segment."
    M.Initial r -> do
      case MapF.lookup r (regIndexMap ctx) of
        Just idx -> do
          getRegInput (macawRegAssign ctx) idx
        Nothing -> fail $ "internal: Register is not bound."
    M.AssignedValue asgn -> do
      let idx = M.assignId asgn
      amap <- use $ crucPStateLens . assignValueMapLens
      case MapF.lookup idx amap of
        Just (MacawCrucibleValue r) -> pure r
        Nothing ->  fail "internal: Assignment id is not bound."

-- | Create a fresh symbolic value of the given type.
freshSymbolic :: M.TypeRepr tp
              -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
freshSymbolic repr = evalMacawStmt (MacawFreshSymbolic repr)

evalMacawStmt :: MacawStmtExtension arch (CR.Atom s) tp -> CrucGen arch ids s (CR.Atom s tp)
evalMacawStmt s = evalAtom (CR.EvalExt s)

-- | Read the given memory address
callReadMem :: M.ArchAddrValue arch ids
            -> M.MemRepr tp
            -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
callReadMem addr repr = do
  caddr <- valueToCrucible addr
  evalMacawStmt (MacawReadMem repr caddr)

callWriteMem :: M.ArchAddrValue arch ids
             -> M.MemRepr tp
             -> M.Value arch ids tp
             -> CrucGen arch ids s ()
callWriteMem addr repr val = do
  caddr <- valueToCrucible addr
  cval  <- valueToCrucible val
  _ <- evalMacawStmt (MacawWriteMem repr caddr cval)
  pure ()

assignRhsToCrucible :: M.AssignRhs arch (M.Value arch ids) tp
                    -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
assignRhsToCrucible rhs =
  case rhs of
    M.EvalApp app -> appToCrucible app
    M.SetUndefined mrepr -> freshSymbolic mrepr
    M.ReadMem addr repr -> callReadMem addr repr
    M.CondReadMem repr c addr def -> do
      undefined repr c addr def
    M.EvalArchFn f _ -> do
      fns <- translateFns <$> get
      crucGenArchFn fns f

addMacawStmt :: M.Stmt arch ids
             -> CrucGen arch ids s ()
addMacawStmt stmt =
  case stmt of
    M.AssignStmt asgn -> do
      let idx = M.assignId asgn
      a <- assignRhsToCrucible (M.assignRhs asgn)
      crucPStateLens . assignValueMapLens %= MapF.insert idx (MacawCrucibleValue a)
    M.WriteMem addr repr val -> do
      callWriteMem addr repr val
    M.PlaceHolderStmt _vals msg -> do
      cmsg <- crucibleValue (C.TextLit (Text.pack msg))
      addTermStmt (CR.ErrorStmt cmsg)
    M.InstructionStart off _ -> do
      -- Update the position
      modify $ \s -> s { codeOff = off }
    M.Comment _txt -> do
      pure ()
    M.ExecArchStmt astmt -> do
      fns <- translateFns <$> get
      crucGenArchStmt fns astmt

lookupCrucibleLabel :: Map Word64 (CR.Label s)
                       -- ^ Map from block index to Crucible label
                    -> Word64
                       -- ^ Index of crucible block
                    -> CrucGen arch ids s (CR.Label s)
lookupCrucibleLabel m idx = do
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

addMacawTermStmt :: Map Word64 (CR.Label s)
                    -- ^ Map from block index to Crucible label
                 -> M.TermStmt arch ids
                 -> CrucGen arch ids s ()
addMacawTermStmt blockLabelMap tstmt =
  case tstmt of
    M.FetchAndExecute regs -> do
      s <- createRegStruct regs
      addTermStmt (CR.Return s)
    M.Branch macawPred macawTrueLbl macawFalseLbl -> do
      p <- valueToCrucible macawPred
      t <- lookupCrucibleLabel blockLabelMap macawTrueLbl
      f <- lookupCrucibleLabel blockLabelMap macawFalseLbl
      addTermStmt (CR.Br p t f)
    M.ArchTermStmt ts regs -> do
      fns <- translateFns <$> get
      crucGenArchTermStmt fns ts regs
    M.TranslateError _regs msg -> do
      cmsg <- crucibleValue (C.TextLit msg)
      addTermStmt (CR.ErrorStmt cmsg)

-----------------

-- | Monad for adding new blocks to a state.
newtype MacawMonad arch ids s a
  = MacawMonad ( ExceptT String (StateT (CrucPersistentState ids s) (ST s)) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError String
           , MonadState (CrucPersistentState ids s)
           )

runMacawMonad :: CrucPersistentState ids s
              -> MacawMonad arch ids s a
              -> ST s (Either String a, CrucPersistentState ids s)
runMacawMonad s (MacawMonad m) = runStateT (runExceptT m) s

mmExecST :: ST s a -> MacawMonad arch ids s a
mmExecST = MacawMonad . lift . lift

runCrucGen :: CrucGenArchFunctions arch
           -> CrucGenContext arch s
           -> (M.ArchAddrWord arch -> C.Position)
              -- ^ Function for generating position from offset from start of this block.
           -> M.ArchAddrWord arch
              -- ^ Offset
           -> CR.Label s
           -> CrucGen arch ids s ()
           -> MacawMonad arch ids s (CR.Block (MacawExt arch) s (MacawFunctionResult arch), M.ArchAddrWord arch)
runCrucGen tfns ctx posFn off lbl action = do
  ps <- get
  let s0 = CrucGenState { translateFns = tfns
                        , crucCtx = ctx
                        , crucPState = ps
                        , macawPositionFn = posFn
                        , blockLabel = lbl
                        , codeOff    = off
                        , prevStmts  = []
                        }
  let cont _s () = fail "Unterminated crucible block"
  (s, tstmt)  <- mmExecST $ unCrucGen action s0 cont
  put (crucPState s)
  let termPos = macawPositionFn s (codeOff s)
  let stmts = Seq.fromList (reverse (prevStmts s))
  let term = C.Posd termPos tstmt
  let blk = CR.mkBlock (CR.LabelID lbl) Set.empty stmts term
  pure (blk, codeOff s)

addMacawBlock :: M.MemWidth (M.ArchAddrWidth arch)
              => CrucGenArchFunctions arch
              -> CrucGenContext arch s
              -> Map Word64 (CR.Label s)
                 -- ^ Map from block index to Crucible label
              -> (M.ArchAddrWord arch -> C.Position)
                 -- ^ Function for generating position from offset from start of this block.
              -> M.Block arch ids
              -> MacawMonad arch ids s (CR.Block (MacawExt arch) s (MacawFunctionResult arch))
addMacawBlock tfns ctx blockLabelMap posFn b = do
  let idx = M.blockLabel b
  lbl <-
    case Map.lookup idx blockLabelMap of
      Just lbl ->
        pure lbl
      Nothing ->
        throwError $ "Internal: Could not find block with index " ++ show idx
  fmap fst $ runCrucGen tfns ctx posFn 0 lbl $ do
    mapM_ addMacawStmt (M.blockStmts b)
    addMacawTermStmt blockLabelMap (M.blockTerm b)

addMacawParsedTermStmt :: M.ParsedTermStmt arch ids
                       -> CrucGen arch ids s ()
addMacawParsedTermStmt tstmt =
  case tstmt of
    M.ParsedCall{} -> undefined
    M.ParsedJump{} -> undefined
    M.ParsedLookupTable{} -> undefined
    M.ParsedReturn{} -> undefined
    M.ParsedIte{} -> undefined
    M.ParsedArchTermStmt{} -> undefined
    M.ParsedTranslateError{} -> undefined
    M.ClassifyFailure{} -> undefined

nextStatements :: M.ParsedTermStmt arch ids -> [M.StatementList arch ids]
nextStatements tstmt =
  case tstmt of
    M.ParsedIte _ x y -> [x, y]
    _ -> []

addStatementList :: M.MemWidth (M.ArchAddrWidth arch)
                 => CrucGenArchFunctions arch
                 -> CrucGenContext arch s
                 -> Map (M.ArchSegmentOff arch, Word64) (CR.Label s)
                 -- ^ Map from block index to Crucible label
                 -> M.ArchSegmentOff arch
                 -- ^ Address of statements
                 -> (M.ArchAddrWord arch -> C.Position)
                    -- ^ Function for generating position from offset from start of this block.
                 -> [(M.ArchAddrWord arch, M.StatementList arch ids)]
                 -> [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
                 -> MacawMonad arch ids s [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
addStatementList _ _ _ _ _ [] rlist =
  pure (reverse rlist)
addStatementList tfns ctx blockLabelMap addr posFn ((off,stmts):rest) r = do
  let idx = M.stmtsIdent stmts
  lbl <-
    case Map.lookup (addr, idx) blockLabelMap of
      Just lbl ->
        pure lbl
      Nothing ->
        throwError $ "Internal: Could not find block with address " ++ show addr ++ " index " ++ show idx
  (b,off') <-
    runCrucGen tfns ctx posFn off lbl $ do
      mapM_ addMacawStmt (M.stmtsNonterm stmts)
      addMacawParsedTermStmt (M.stmtsTerm stmts)
  let new = (off',) <$> nextStatements (M.stmtsTerm stmts)
  addStatementList tfns ctx blockLabelMap addr posFn (new ++ rest) (b:r)

addParsedBlock :: forall arch ids s
               .  M.MemWidth (M.ArchAddrWidth arch)
               => CrucGenArchFunctions arch
               -> CrucGenContext arch s
               -> Map (M.ArchSegmentOff arch, Word64) (CR.Label s)
               -- ^ Map from block index to Crucible label
               -> (M.ArchSegmentOff arch -> C.Position)
               -- ^ Function for generating position from offset from start of this block.
               -> M.ParsedBlock arch ids
               -> MacawMonad arch ids s [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
addParsedBlock tfns ctx blockLabelMap posFn b = do
  let base = M.pblockAddr b
  let thisPosFn :: M.ArchAddrWord arch -> C.Position
      thisPosFn off = posFn r
        where Just r = M.incSegmentOff base (toInteger off)
  addStatementList tfns ctx blockLabelMap (M.pblockAddr b) thisPosFn [(0, M.blockStatementList b)] []
