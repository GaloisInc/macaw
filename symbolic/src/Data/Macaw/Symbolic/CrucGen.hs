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
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Symbolic.CrucGen
  ( MacawSymbolicArchFunctions(..)
  , crucArchRegTypes
  , MacawExt
  , MacawExprExtension(..)
  , MacawOverflowOp(..)
  , MacawStmtExtension(..)
  , MacawFunctionArgs
  , MacawFunctionResult
  , ArchAddrCrucibleType
  , MacawCrucibleRegTypes
  , ArchRegStruct
  , MacawArchConstraints
  , MacawArchStmtExtension
    -- ** Operations for implementing new backends.
  , CrucGen
  , MacawMonad
  , runMacawMonad
  , addMacawBlock
  , BlockLabelMap
  , addParsedBlock
  , nextStatements
  , valueToCrucible
  , evalArchStmt
  , MemSegmentMap
  ) where

import           Control.Lens hiding (Empty, (:>))
import           Control.Monad.Except
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Bits
import           Data.Proxy(Proxy(..))
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.CFG.Block as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Types as M
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
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

import qualified Lang.Crucible.LLVM.MemModel as MM

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.Symbolic.PersistentState


-- | List of crucible types for architecture.
type MacawCrucibleRegTypes (arch :: *) =
        CtxToCrucibleType arch (ArchRegContext arch)

type ArchRegStruct (arch :: *) = C.StructType (MacawCrucibleRegTypes arch)

type ArchAddrCrucibleType arch = MM.LLVMPointerType (M.ArchAddrWidth arch)

type MacawFunctionArgs arch = EmptyCtx ::> ArchRegStruct arch
type MacawFunctionResult arch = ArchRegStruct arch

type family MacawArchStmtExtension (arch :: *) :: (C.CrucibleType -> *) -> C.CrucibleType -> *

type MacawArchConstraints arch =
  ( TraversableFC (MacawArchStmtExtension arch)
  , C.TypeApp (MacawArchStmtExtension arch)
  , C.PrettyApp (MacawArchStmtExtension arch)
  )

------------------------------------------------------------------------
-- CrucPersistentState


-- | Architecture-specific information needed to translate from Macaw to Crucible
data MacawSymbolicArchFunctions arch
  = MacawSymbolicArchFunctions
  { crucGenArchConstraints
    :: !(forall a . ((M.RegisterInfo (M.ArchReg arch), MacawArchConstraints arch) => a) -> a)
  , crucGenRegAssignment :: !(Ctx.Assignment (M.ArchReg arch) (ArchRegContext arch))
    -- ^ Map from indices in the ArchRegContext to the associated register.
  , crucGenArchRegName :: !(forall tp . M.ArchReg arch tp -> C.SolverSymbol)
    -- ^ Provides a solver name to use for referring to register.
  , crucGenArchFn :: !(forall ids s tp
                         . M.ArchFn arch (M.Value arch ids) tp
                         -> CrucGen arch ids s (CR.Atom s (ToCrucibleType arch tp)))
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

-- | Return types of registers in Crucible
crucArchRegTypes :: MacawSymbolicArchFunctions arch
                 -> Assignment C.TypeRepr (CtxToCrucibleType arch (ArchRegContext arch))
crucArchRegTypes archFns = crucGenArchConstraints archFns $
    typeCtxToCrucible archFns (fmapFC M.typeRepr regAssign)
  where regAssign = crucGenRegAssignment archFns

------------------------------------------------------------------------
-- MacawExprExtension

data MacawOverflowOp
   = Uadc
   | Sadc
   | Usbb
   | Ssbb
  deriving (Eq, Ord, Show)

data MacawExprExtension (arch :: *)
                        (f :: C.CrucibleType -> *)
                        (tp :: C.CrucibleType)
  where
  MacawOverflows :: (1 <= w)
                 => !MacawOverflowOp
                 -> !(NatRepr w)
                 -> !(f (C.BVType w))
                 -> !(f (C.BVType w))
                 -> !(f C.BoolType)
                 -> MacawExprExtension arch f C.BoolType

  -- | Treat a pointer as a number.
  PtrToBits ::
    (1 <= w) =>
    !(f (MM.LLVMPointerType w)) ->
    MacawExprExtension arch f (C.BVType w)

  -- | Treat a number as a pointer.
  -- We can never read from this pointer.
  BitsToPtr ::
    (1 <= w) =>
    !(f (C.BVType w)) ->
    MacawExprExtension arch f (MM.LLVMPointerType w)

  

instance C.PrettyApp (MacawExprExtension arch) where
  ppApp f a0 =
    case a0 of
      MacawOverflows o w x y c ->
        let mnem = "macawOverflows_" ++ show o ++ "_" ++ show w
         in sexpr mnem [f x, f y, f c]

      -- XXX: PtrToBits, BitsToPtr

instance C.TypeApp (MacawExprExtension arch) where
  appType (MacawOverflows _ _ _ _ _) = C.knownRepr
      -- XXX: PtrToBits, BitsToPtr

instance TestEqualityFC (MacawExprExtension arch) where
  testEqualityFC f (MacawOverflows xo xw xa xb xc)
                   (MacawOverflows yo yw ya yb yc) = do
    when (xo /= yo) $ Nothing
    Refl <- testEquality xw yw
    Refl <- f xa ya
    Refl <- f xb yb
    Refl <- f xc yc
    pure Refl
      -- XXX: PtrToBits, BitsToPtr

instance OrdFC (MacawExprExtension arch) where
  compareFC f (MacawOverflows xo xw xa xb xc)
              (MacawOverflows yo yw ya yb yc) =
    joinOrderingF (fromOrdering (compare xo yo)) $
    joinOrderingF (compareF xw yw) $
    joinOrderingF (f xa ya) $
    joinOrderingF (f xb yb) $
    joinOrderingF (f xc yc) $
    EQF
  -- XXX: PtrToBits, BitsToPtr

instance FunctorFC (MacawExprExtension arch) where
  fmapFC = fmapFCDefault
instance FoldableFC (MacawExprExtension arch) where
  foldMapFC = foldMapFCDefault
instance TraversableFC (MacawExprExtension arch) where
  traverseFC f (MacawOverflows o w a b c) =
    MacawOverflows o w <$> f a <*> f b <*> f c
  -- XXX: PtrToBits, BitsToPtr

------------------------------------------------------------------------
-- MacawStmtExtension

data MacawStmtExtension (arch :: *)
                        (f    :: C.CrucibleType -> *)
                        (tp   :: C.CrucibleType)
  where

  -- | Read from memory.
  MacawReadMem ::

    -- | Info about memory (endianness, size)
    !(M.MemRepr tp) ->

    -- | Pointer to read from.
    !(f (ArchAddrCrucibleType arch)) ->

    MacawStmtExtension arch f (ToCrucibleType arch tp)


  -- | Read from memory, if the condition is True.
  -- Otherwise, just return the given value.
  MacawCondReadMem ::

    -- | Info about memory (endianness, size)
    !(M.MemRepr tp) ->

    -- | Condition
    !(f C.BoolType) ->

    -- | Pointer to read from
    !(f (ArchAddrCrucibleType arch)) ->

    -- | Default value, returned if the condition is False.
    !(f (ToCrucibleType arch tp)) ->

    MacawStmtExtension arch f (ToCrucibleType arch tp)

  -- | Write to memory
  MacawWriteMem ::
    !(M.MemRepr tp) ->
    !(f (ArchAddrCrucibleType arch)) ->
    !(f (ToCrucibleType arch tp)) ->
    MacawStmtExtension arch f C.UnitType

  -- | Generate a fresh symbolic variable of the given type.
  MacawFreshSymbolic ::
    !(M.TypeRepr tp) -> MacawStmtExtension arch f (ToCrucibleType arch tp)

  -- | Call a function.
  MacawCall ::
    -- | Types of fields in register struct
    !(Assignment C.TypeRepr (CtxToCrucibleType arch (ArchRegContext arch))) ->

    -- | Arguments to call.
    !(f (ArchRegStruct arch)) ->

    MacawStmtExtension arch f (ArchRegStruct arch)

  -- | A machine instruction.
  MacawArchStmtExtension ::
    !(MacawArchStmtExtension arch f tp) ->
    MacawStmtExtension arch f tp

stmtArch :: MacawStmtExtension arch f p -> Proxy arch
stmtArch _ = Proxy


instance TraversableFC (MacawArchStmtExtension arch)
      => FunctorFC (MacawStmtExtension arch) where
  fmapFC = fmapFCDefault

instance TraversableFC (MacawArchStmtExtension arch)
      => FoldableFC (MacawStmtExtension arch) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (MacawArchStmtExtension arch)
      => TraversableFC (MacawStmtExtension arch) where
  traverseFC f a0 =
    case a0 of
      MacawReadMem  r a   -> MacawReadMem r <$> f a
      MacawCondReadMem r c a d -> MacawCondReadMem r <$> f c <*> f a <*> f d
      MacawWriteMem r a v -> MacawWriteMem r <$> f a <*> f v
      MacawFreshSymbolic r -> pure (MacawFreshSymbolic r)
      MacawCall regTypes regs -> MacawCall regTypes <$> f regs
      MacawArchStmtExtension a ->
        MacawArchStmtExtension <$> traverseFC f a


sexpr :: String -> [Doc] -> Doc
sexpr s [] = text s
sexpr s l  = parens (text s <+> hsep l)

instance C.PrettyApp (MacawArchStmtExtension arch)
      => C.PrettyApp (MacawStmtExtension arch) where
  ppApp f a0 =
    case a0 of
      MacawReadMem r a     -> sexpr "macawReadMem"       [pretty r, f a]
      MacawCondReadMem r c a d -> sexpr "macawCondReadMem" [pretty r, f c, f a, f d ]
      MacawWriteMem r a v  -> sexpr "macawWriteMem"      [pretty r, f a, f v]
      MacawFreshSymbolic r -> sexpr "macawFreshSymbolic" [ text (show r) ]
      MacawCall _ regs -> sexpr "macawCall" [ f regs ]
      MacawArchStmtExtension a -> C.ppApp f a

instance C.TypeApp (MacawArchStmtExtension arch)
      => C.TypeApp (MacawStmtExtension arch) where
  appType s@(MacawReadMem r _) = memReprToCrucible (stmtArch s) r
  appType s@(MacawCondReadMem r _ _ _) = memReprToCrucible (stmtArch s) r
  appType (MacawWriteMem _ _ _) = C.knownRepr
  appType s@(MacawFreshSymbolic r) = typeToCrucible (stmtArch s) r
  appType (MacawCall regTypes _) = C.StructRepr regTypes
  appType s@(MacawArchStmtExtension f) = C.appType f

------------------------------------------------------------------------
-- MacawExt

data MacawExt (arch :: *)

type instance C.ExprExtension (MacawExt arch) = MacawExprExtension arch
type instance C.StmtExtension (MacawExt arch) = MacawStmtExtension arch

instance MacawArchConstraints arch
      => C.IsSyntaxExtension (MacawExt arch)

-- | Map from indices of segments without a fixed base address to a
-- global variable storing the base address.
--
-- This uses a global variable so that we can do the translation, and then
-- decide where to locate it without requiring us to also pass the values
-- around arguments.
type MemSegmentMap w = Map M.RegionIndex (CR.GlobalVar (C.BVType w))

-- | State used for generating blocks
data CrucGenState arch ids s
   = CrucGenState
   { translateFns       :: !(MacawSymbolicArchFunctions arch)
   , crucMemBaseAddrMap :: !(MemSegmentMap (M.ArchAddrWidth arch))
     -- ^ Map from memory region to base address
   , crucRegIndexMap :: !(RegIndexMap arch)
     -- ^ Map from architecture register to Crucible/Macaw index pair.
   , crucPState      :: !(CrucPersistentState arch ids s)
     -- ^ State that persists across blocks.
   , crucRegisterReg :: !(CR.Reg s (ArchRegStruct arch))
   , macawPositionFn :: !(M.ArchAddrWord arch -> C.Position)
     -- ^ Map from offset to Crucible position.
   , blockLabel :: (CR.Label s)
     -- ^ Label for this block we are translating
   , codeOff    :: !(M.ArchAddrWord arch)
     -- ^ Offset
   , prevStmts  :: ![C.Posd (CR.Stmt (MacawExt arch) s)]
     -- ^ List of states in reverse order
   }

crucPStateLens ::
  Simple Lens (CrucGenState arch ids s) (CrucPersistentState arch ids s)
crucPStateLens = lens crucPState (\s v -> s { crucPState = v })

assignValueMapLens ::
  Simple Lens (CrucPersistentState arch ids s)
              (MapF (M.AssignId ids) (MacawCrucibleValue arch (CR.Atom s)))
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
  archFns <- gets translateFns
  crucGenArchConstraints archFns $ do
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
crucibleValue = evalAtom . CR.EvalApp

-- | Evaluate a Macaw expression extension
evalMacawExt :: MacawExprExtension arch (CR.Atom s) tp -> CrucGen arch ids s (CR.Atom s tp)
evalMacawExt = crucibleValue . C.ExtensionApp

-- | Treat a register value as a bit-vector.
toBits ::
  (1 <= w) =>
  CR.Atom s (MM.LLVMPointerType w) ->
  CrucGen arch ids s (CR.Atom s (C.BVType w))
toBits x = evalMacawExt (PtrToBits x)

-- | Treat a bit-vector as a register value.
fromBits ::
  (1 <= w) =>
  CR.Atom s (C.BVType w) ->
  CrucGen arch ids s (CR.Atom s (MM.LLVMPointerType w))
fromBits x = evalMacawExt (BitsToPtr x)


getArch :: CrucGen arch ids s (Proxy arch)
getArch = return Proxy


-- | Return the value associated with the given register
getRegValue :: M.ArchReg arch tp
            -> CrucGen arch ids s (CR.Atom s (ToCrucibleType arch tp))
getRegValue r = do
  archFns <- gets translateFns
  idxMap  <- gets crucRegIndexMap
  crucGenArchConstraints archFns $ do
  case MapF.lookup r idxMap of
    Nothing -> fail $ "internal: Register is not bound."
    Just idx -> do
      reg <- gets crucRegisterReg
      regStruct <- evalAtom (CR.ReadReg reg)
      let tp = M.typeRepr (crucGenRegAssignment archFns Ctx.! macawIndex idx)
      arch <- getArch
      crucibleValue (C.GetStruct regStruct (crucibleIndex idx)
                    (typeToCrucible arch tp))

v2c :: M.Value arch ids tp
    -> CrucGen arch ids s (CR.Atom s (ToCrucibleType arch tp))
v2c = valueToCrucible

v2c' :: (1 <= w) =>
       M.Value arch ids (M.BVType w) ->
       CrucGen arch ids s (CR.Atom s (C.BVType w))
v2c' x = toBits =<< valueToCrucible x

-- | Evaluate the crucible app and return a reference to the result.
appAtom :: C.App (MacawExt arch) (CR.Atom s) ctp ->
            CrucGen arch ids s (CR.Atom s ctp)
appAtom app = evalAtom (CR.EvalApp app)

addLemma :: (1 <= x, x + 1 <= y) => p x -> q y -> LeqProof 1 y
addLemma _ _ = undefined


-- | Create a crucible value for a bitvector literal.
bvLit :: (1 <= w) => NatRepr w -> Integer -> CrucGen arch ids s (CR.Atom s (C.BVType w))
bvLit w i = crucibleValue (C.BVLit w (i .&. maxUnsigned w))


bitOp1 ::
  (1 <= v, 1 <= w) =>
  (CR.Atom s (C.BVType v) -> C.App (MacawExt arch) (CR.Atom s) (C.BVType w)) ->
  M.Value arch ids (M.BVType v) ->
  CrucGen arch ids s (CR.Atom s (MM.LLVMPointerType w))
bitOp1 f x =
  do v <- v2c' x
     res <- appAtom (f v)
     fromBits res

bitOp2' ::
  (1 <= u, 1 <= v) =>
  (CR.Atom s (C.BVType u) ->
   CR.Atom s (C.BVType v) ->
   C.App (MacawExt arch) (CR.Atom s) t) ->
   M.Value arch ids (M.BVType u) ->
   M.Value arch ids (M.BVType v) ->
   CrucGen arch ids s (CR.Atom s t)
bitOp2' f x y =
  do x' <- v2c' x
     y' <- v2c' y
     appAtom (f x' y')

bitOp2 ::
  (1 <= u, 1 <= v, 1 <= w) =>
  (CR.Atom s (C.BVType u) ->
   CR.Atom s (C.BVType v) ->
   C.App (MacawExt arch) (CR.Atom s) (C.BVType w)) ->
   M.Value arch ids (M.BVType u) ->
   M.Value arch ids (M.BVType v) ->
   CrucGen arch ids s (CR.Atom s (MM.LLVMPointerType w))
bitOp2 f x y = fromBits =<< bitOp2' f x y




appToCrucible :: M.App (M.Value arch ids) tp ->
                  CrucGen arch ids s (CR.Atom s (ToCrucibleType arch tp))
appToCrucible app = do
  archFns <- gets translateFns
  crucGenArchConstraints archFns $ do
  case app of

{-
    M.Eq x y -> do
      let btp = typeToCrucible (M.typeRepr x)
      appAtom =<< C.BaseIsEq btp <$> v2c x <*> v2c y
    M.Mux tp c t f -> do
      let btp = undefined -- typeToCrucibleBase tp
      appAtom =<< C.BaseIte btp <$> v2c c <*> v2c t <*> v2c f

    M.TupleField tps x i ->
      undefined tps x i -- TODO: Fix this
-}

    -- Booleans

    M.AndApp x y  -> appAtom =<< C.And     <$> v2c x <*> v2c y
    M.OrApp  x y  -> appAtom =<< C.Or      <$> v2c x <*> v2c y
    M.NotApp x    -> appAtom =<< C.Not     <$> v2c x
    M.XorApp x y  -> appAtom =<< C.BoolXor <$> v2c x <*> v2c y

    -- Extension operations
    M.Trunc x w ->
      do let w1 = M.typeWidth x
         LeqProof <- return (addLemma w w1)
         bitOp1 (C.BVTrunc w w1) x

    M.SExt x w -> bitOp1 (C.BVSext w (M.typeWidth x)) x
    M.UExt x w -> bitOp1 (C.BVZext w (M.typeWidth x)) x

{-
    -- Bitvector arithmetic
    M.BVAdd w x y -> appAtom =<< C.BVAdd w <$> v2c x <*> v2c y
-}

    -- Here we assume that this does not make sense for pointers.
    M.BVAdc w x y c -> do
      z <- appAtom =<< C.BVAdd w <$> v2c' x <*> v2c' y
      d <- appAtom =<< C.BaseIte (C.BaseBVRepr w) <$> v2c c
                                             <*> appAtom (C.BVLit w 1)
                                             <*> appAtom (C.BVLit w 0)
      fromBits =<< appAtom (C.BVAdd w z d)
{-
    M.BVSub w x y -> appAtom =<< C.BVSub w <$> v2c x <*> v2c y
    M.BVSbb w x y c -> do
      z <- appAtom =<< C.BVSub w <$> v2c x <*> v2c y
      d <- appAtom =<< C.BaseIte (C.BaseBVRepr w) <$> v2c c
                                             <*> appAtom (C.BVLit w 1)
                                             <*> appAtom (C.BVLit w 0)
      appAtom $ C.BVSub w z d

-}

    M.BVMul w x y -> bitOp2 (C.BVMul w) x y

    M.BVUnsignedLe x y -> bitOp2' (C.BVUle (M.typeWidth x)) x y
    M.BVUnsignedLt x y -> bitOp2' (C.BVUlt (M.typeWidth x)) x y
    M.BVSignedLe   x y -> bitOp2' (C.BVSle (M.typeWidth x)) x y
    M.BVSignedLt   x y -> bitOp2' (C.BVSlt (M.typeWidth x)) x y

    -- Bitwise operations
    M.BVTestBit x i -> do
      let w = M.typeWidth x
      one <- bvLit w 1
      -- Create mask for ith index
      i_mask <- appAtom =<< C.BVShl w one <$> (toBits =<< v2c i)
      -- Mask off index
      x_mask <- appAtom =<< C.BVAnd w <$> (toBits =<< v2c x) <*> pure i_mask
      -- Check to see if result is i_mask
      appAtom (C.BVEq w x_mask i_mask)

    M.BVComplement w x -> bitOp1 (C.BVNot w) x

    M.BVAnd w x y -> bitOp2 (C.BVAnd  w) x y
    M.BVOr  w x y -> bitOp2 (C.BVOr   w) x y
    M.BVXor w x y -> bitOp2 (C.BVXor  w) x y
    M.BVShl w x y -> bitOp2 (C.BVShl  w) x y
    M.BVShr w x y -> bitOp2 (C.BVLshr w) x y
    M.BVSar w x y -> bitOp2 (C.BVAshr w) x y

    M.UadcOverflows x y c -> do
      r <- MacawOverflows Uadc (M.typeWidth x) <$> v2c' x <*> v2c' y <*> v2c c
      evalMacawExt r
    M.SadcOverflows x y c -> do
      r <- MacawOverflows Sadc (M.typeWidth x) <$> v2c' x <*> v2c' y <*> v2c c
      evalMacawExt r
    M.UsbbOverflows x y b -> do
      r <- MacawOverflows Usbb (M.typeWidth x) <$> v2c' x <*> v2c' y <*> v2c b
      evalMacawExt r
    M.SsbbOverflows x y b -> do
      r <- MacawOverflows Ssbb (M.typeWidth x) <$> v2c' x <*> v2c' y <*> v2c b
      evalMacawExt r
    M.PopCount w x -> do
      undefined w x
    M.ReverseBytes w x -> do
      undefined w x
    M.Bsf w x -> do
      undefined w x
    M.Bsr w x -> do
      undefined w x



valueToCrucible :: M.Value arch ids tp
                -> CrucGen arch ids s (CR.Atom s (ToCrucibleType arch tp))
valueToCrucible v = do
 archFns <- gets translateFns
 crucGenArchConstraints archFns $ do
 case v of
    M.BVValue w c -> fromBits =<< bvLit w c
    M.BoolValue b -> crucibleValue (C.BoolLit b)

    M.RelocatableValue {} -> fail "XXX: Deal with globals"

{-
    -- In this case,
    M.RelocatableValue w addr
      | M.addrBase addr == 0 -> do
          crucibleValue (C.BVLit w (toInteger (M.addrOffset addr)))
      | otherwise -> do
          let idx = M.addrBase addr
          segMap <- gets crucMemBaseAddrMap
          case Map.lookup idx segMap of
            Just g -> do
              a <- evalAtom (CR.ReadGlobal g)
              offset <- crucibleValue (C.BVLit w (toInteger (M.addrOffset addr)))
              crucibleValue (C.BVAdd w a offset)
            Nothing ->
              fail $ "internal: No Crucible address associated with segment."
-}
    M.Initial r ->
      getRegValue r

    M.AssignedValue asgn -> do
      let idx = M.assignId asgn
      amap <- use $ crucPStateLens . assignValueMapLens
      case MapF.lookup idx amap of
        Just (MacawCrucibleValue r) -> pure r
        Nothing ->  fail "internal: Assignment id is not bound."

-- | Create a fresh symbolic value of the given type.
freshSymbolic :: M.TypeRepr tp
              -> CrucGen arch ids s (CR.Atom s (ToCrucibleType arch tp))
freshSymbolic repr = evalMacawStmt (MacawFreshSymbolic repr)

evalMacawStmt :: MacawStmtExtension arch (CR.Atom s) tp ->
                  CrucGen arch ids s (CR.Atom s tp)
evalMacawStmt = evalAtom . CR.EvalExt

evalArchStmt :: MacawArchStmtExtension arch (CR.Atom s) tp -> CrucGen arch ids s (CR.Atom s tp)
evalArchStmt = evalMacawStmt . MacawArchStmtExtension

assignRhsToCrucible :: M.AssignRhs arch (M.Value arch ids) tp
                    -> CrucGen arch ids s (CR.Atom s (ToCrucibleType arch tp))
assignRhsToCrucible rhs =
  case rhs of
    M.EvalApp app -> appToCrucible app
    M.SetUndefined mrepr -> freshSymbolic mrepr
    M.ReadMem addr repr -> do
      caddr <- valueToCrucible addr
      evalMacawStmt (MacawReadMem repr caddr)
    M.CondReadMem repr cond addr def -> do
      ccond <- valueToCrucible cond
      caddr <- valueToCrucible addr
      cdef <- valueToCrucible def
      evalMacawStmt (MacawCondReadMem repr ccond caddr cdef)
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
      caddr <- valueToCrucible addr
      cval  <- valueToCrucible val
      void $ evalMacawStmt (MacawWriteMem repr caddr cval)
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
  archFns <- gets translateFns
  crucGenArchConstraints archFns $ do
  let regAssign = crucGenRegAssignment archFns
  let tps = fmapFC M.typeRepr regAssign
  let a = fmapFC (\r -> regs ^. M.boundValue r) regAssign
  arch <- getArch
  fields <- macawAssignToCrucM arch valueToCrucible a
  crucibleValue $ C.MkStruct (typeCtxToCrucible arch tps) fields

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
  = MacawMonad ( ExceptT String (StateT (CrucPersistentState arch ids s) (ST s)) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError String
           , MonadState (CrucPersistentState arch ids s)
           )

runMacawMonad :: CrucPersistentState arch ids s
              -> MacawMonad arch ids s a
              -> ST s (Either String a, CrucPersistentState arch ids s)
runMacawMonad s (MacawMonad m) = runStateT (runExceptT m) s

mmExecST :: ST s a -> MacawMonad arch ids s a
mmExecST = MacawMonad . lift . lift

runCrucGen :: forall arch ids s
           .  MacawSymbolicArchFunctions arch
           -> MemSegmentMap (M.ArchAddrWidth arch)
              -- ^ Base address map
           -> (M.ArchAddrWord arch -> C.Position)
              -- ^ Function for generating position from offset from start of this block.
           -> M.ArchAddrWord arch
              -- ^ Offset of this block
           -> CR.Label s
              -- ^ Label for this block
           -> CR.Reg s (ArchRegStruct arch)
              -- ^ Crucible register for struct containing all Macaw registers.
           -> CrucGen arch ids s ()
           -> MacawMonad arch ids s (CR.Block (MacawExt arch) s (MacawFunctionResult arch), M.ArchAddrWord arch)
runCrucGen archFns baseAddrMap posFn off lbl regReg action = crucGenArchConstraints archFns $ do
  ps <- get
  let regAssign = crucGenRegAssignment archFns
  let crucRegTypes = crucArchRegTypes archFns
  let s0 = CrucGenState { translateFns = archFns
                        , crucMemBaseAddrMap = baseAddrMap
                        , crucRegIndexMap = mkRegIndexMap regAssign (Ctx.size crucRegTypes)
                        , crucPState = ps
                        , crucRegisterReg = regReg
                        , macawPositionFn = posFn
                        , blockLabel = lbl
                        , codeOff    = off
                        , prevStmts  = []
                        }
  let cont _s () = fail "Unterminated crucible block"
  (s, tstmt)  <- mmExecST $ unCrucGen action s0 cont
  put (crucPState s)
  let termPos = posFn (codeOff s)
  let stmts = Seq.fromList (reverse (prevStmts s))
  let term = C.Posd termPos tstmt
  let blk = CR.mkBlock (CR.LabelID lbl) Set.empty stmts term
  pure (blk, codeOff s)

addMacawBlock :: M.MemWidth (M.ArchAddrWidth arch)
              => MacawSymbolicArchFunctions arch
              -> MemSegmentMap (M.ArchAddrWidth arch)
              -- ^ Base address map
              -> Map Word64 (CR.Label s)
                 -- ^ Map from block index to Crucible label
              -> (M.ArchAddrWord arch -> C.Position)
                 -- ^ Function for generating position from offset from start of this block.
              -> M.Block arch ids
              -> MacawMonad arch ids s (CR.Block (MacawExt arch) s (MacawFunctionResult arch))
addMacawBlock archFns baseAddrMap blockLabelMap posFn b = do
  let idx = M.blockLabel b
  lbl <-
    case Map.lookup idx blockLabelMap of
      Just lbl ->
        pure lbl
      Nothing ->
        throwError $ "Internal: Could not find block with index " ++ show idx
  let archRegStructRepr = C.StructRepr (crucArchRegTypes archFns)
  let regReg = CR.Reg { CR.regPosition = posFn 0
                      , CR.regId = 0
                      , CR.typeOfReg = archRegStructRepr
                      }
  let regStruct = CR.Atom { CR.atomPosition = C.InternalPos
                          , CR.atomId = 0
                          , CR.atomSource = CR.FnInput
                          , CR.typeOfAtom = archRegStructRepr
                          }
  fmap fst $ runCrucGen archFns baseAddrMap posFn 0 lbl regReg $ do
    addStmt $ CR.SetReg regReg regStruct
    mapM_ addMacawStmt (M.blockStmts b)
    addMacawTermStmt blockLabelMap (M.blockTerm b)

parsedBlockLabel :: (Ord addr, Show addr)
                 => Map (addr, Word64) (CR.Label s)
                    -- ^ Map from block addresses to starting label
                 -> addr
                 -> Word64
                 -> CR.Label s
parsedBlockLabel blockLabelMap addr idx =
  fromMaybe (error $ "Could not find entry point: " ++ show addr) $
  Map.lookup (addr, idx) blockLabelMap

setMachineRegs :: CR.Atom s (ArchRegStruct arch) -> CrucGen arch ids s ()
setMachineRegs newRegs = do
  regReg <- gets crucRegisterReg
  addStmt $ CR.SetReg regReg newRegs

-- | Map from block information to Crucible label (used to generate term statements)
type BlockLabelMap arch s = Map (M.ArchSegmentOff arch, Word64) (CR.Label s)

addMacawParsedTermStmt :: BlockLabelMap arch s
                          -- ^ Block label map for this function
                       -> M.ArchSegmentOff arch
                          -- ^ Address of this block
                       -> M.ParsedTermStmt arch ids
                       -> CrucGen arch ids s ()
addMacawParsedTermStmt blockLabelMap thisAddr tstmt = do
 archFns <- translateFns <$> get
 crucGenArchConstraints archFns $ do
  case tstmt of
    M.ParsedCall regs mret -> do
      curRegs <- createRegStruct regs
      newRegs <- evalMacawStmt (MacawCall (crucArchRegTypes archFns) curRegs)
      case mret of
        Just nextAddr -> do
          setMachineRegs newRegs
          addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap nextAddr 0)
        Nothing ->
          addTermStmt $ CR.Return newRegs
    M.ParsedJump regs nextAddr -> do
      setMachineRegs =<< createRegStruct regs
      addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap nextAddr 0)
    M.ParsedLookupTable regs _idx _possibleAddrs -> do
      setMachineRegs =<< createRegStruct regs
      let cond = undefined
      -- TODO: Add ability in CrucGen to generate new labels and add new blocks.
      let tlbl = undefined
      let flbl = undefined
      addTermStmt $! CR.Br cond tlbl flbl
    M.ParsedReturn regs -> do
      regValues <- createRegStruct regs
      addTermStmt $ CR.Return regValues
    M.ParsedIte c t f -> do
      crucCond <- valueToCrucible c
      let tlbl = parsedBlockLabel blockLabelMap thisAddr (M.stmtsIdent t)
      let flbl = parsedBlockLabel blockLabelMap thisAddr (M.stmtsIdent f)
      addTermStmt $! CR.Br crucCond tlbl flbl
    M.ParsedArchTermStmt aterm regs _mret -> do
      crucGenArchTermStmt archFns aterm regs
    M.ParsedTranslateError msg -> do
      msgVal <- crucibleValue (C.TextLit msg)
      addTermStmt $ CR.ErrorStmt msgVal
    M.ClassifyFailure _regs -> do
      msgVal <- crucibleValue $ C.TextLit $ Text.pack $ "Could not identify block at " ++ show thisAddr
      addTermStmt $ CR.ErrorStmt msgVal

nextStatements :: M.ParsedTermStmt arch ids -> [M.StatementList arch ids]
nextStatements tstmt =
  case tstmt of
    M.ParsedIte _ x y -> [x, y]
    _ -> []

addStatementList :: MacawSymbolicArchFunctions arch
                 -> MemSegmentMap (M.ArchAddrWidth arch)
                 -- ^ Base address map
                 -> BlockLabelMap arch s
                 -- ^ Map from block index to Crucible label
                 -> M.ArchSegmentOff arch
                 -- ^ Address of block that starts statements
                 -> (M.ArchAddrWord arch -> C.Position)
                    -- ^ Function for generating position from offset from start of this block.
                 -> CR.Reg s (ArchRegStruct arch)
                    -- ^ Register that stores Macaw registers
                 -> [(M.ArchAddrWord arch, M.StatementList arch ids)]
                 -> [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
                 -> MacawMonad arch ids s [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
addStatementList _ _ _ _ _ _ [] rlist =
  pure (reverse rlist)
addStatementList archFns baseAddrMap blockLabelMap startAddr posFn regReg ((off,stmts):rest) r = do
  crucGenArchConstraints archFns $ do
  let idx = M.stmtsIdent stmts
  lbl <-
    case Map.lookup (startAddr, idx) blockLabelMap of
      Just lbl ->
        pure lbl
      Nothing ->
        throwError $ "Internal: Could not find block with address " ++ show startAddr ++ " index " ++ show idx
  (b,off') <-
    runCrucGen archFns baseAddrMap posFn off lbl regReg $ do
      mapM_ addMacawStmt (M.stmtsNonterm stmts)
      addMacawParsedTermStmt blockLabelMap startAddr (M.stmtsTerm stmts)
  let new = (off',) <$> nextStatements (M.stmtsTerm stmts)
  addStatementList archFns baseAddrMap blockLabelMap startAddr posFn regReg (new ++ rest) (b:r)

addParsedBlock :: forall arch ids s
               .  MacawSymbolicArchFunctions arch
               -> MemSegmentMap (M.ArchAddrWidth arch)
               -- ^ Base address map
               -> BlockLabelMap arch s
               -- ^ Map from block index to Crucible label
               -> (M.ArchSegmentOff arch -> C.Position)
               -- ^ Function for generating position from offset from start of this block.
               -> CR.Reg s (ArchRegStruct arch)
                    -- ^ Register that stores Macaw registers
               -> M.ParsedBlock arch ids
               -> MacawMonad arch ids s [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
addParsedBlock tfns baseAddrMap blockLabelMap posFn regReg b = do
  crucGenArchConstraints tfns $ do
  let base = M.pblockAddr b
  let thisPosFn :: M.ArchAddrWord arch -> C.Position
      thisPosFn off = posFn r
        where Just r = M.incSegmentOff base (toInteger off)
  addStatementList tfns baseAddrMap blockLabelMap
    (M.pblockAddr b) thisPosFn regReg [(0, M.blockStatementList b)] []
