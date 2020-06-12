{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType #-}
#endif
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.Symbolic.MemTraceOps where

import           Control.Applicative
import           Control.Lens ((%~), (&), (^.))
import           Control.Monad.State
import qualified Data.BitVector.Sized as BV
import           Data.List
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Vector as V
import           GHC.TypeNats (KnownNat)
import           Numeric

import Data.Macaw.CFG.AssignRhs (ArchAddrWidth, MemRepr(..))
import Data.Macaw.Memory (AddrWidthRepr(..), Endianness, addrWidthClass, addrWidthNatRepr)
import Data.Macaw.Symbolic.Backend (EvalStmtFunc, MacawArchEvalFn(..))
import Data.Macaw.Symbolic.CrucGen (MacawStmtExtension(..), MacawExt)
import Data.Macaw.Symbolic.MemOps (GlobalMap, MacawSimulatorState(..), doGetGlobal)
import Data.Macaw.Symbolic.PersistentState (ToCrucibleType)
import Data.Parameterized.Context (pattern (:>), pattern Empty)
import qualified Data.Parameterized.Map as MapF
import Data.Text (pack)
import Lang.Crucible.Backend (IsSymInterface, assert)
import Lang.Crucible.CFG.Common (GlobalVar, freshGlobalVar)
import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.LLVM.MemModel (LLVMPointerType, LLVMPtr, pattern LLVMPointer, llvmPointer_bv)
import Lang.Crucible.Simulator.ExecutionTree (CrucibleState, actFrame, gpGlobals, stateSymInterface, stateTree)
import Lang.Crucible.Simulator.GlobalState (insertGlobal, lookupGlobal)
import Lang.Crucible.Simulator.Intrinsics (IntrinsicClass(..), IntrinsicMuxFn(..), IntrinsicTypes)
import Lang.Crucible.Simulator.RegMap (RegEntry(..))
import Lang.Crucible.Simulator.RegValue (RegValue)
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import Lang.Crucible.Types ((::>), BoolType, BVType, EmptyCtx, IntrinsicType, SymbolRepr, TypeRepr(BVRepr), knownSymbol)
import What4.Concrete (ConcreteVal(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Interface -- (NatRepr, knownRepr, BaseTypeRepr(..), SolverSymbol, userSymbol, freshConstant, natLit)

data MemOpCondition sym
  = Unconditional
  | Conditional (Pred sym)

deriving instance Show (Pred sym) => Show (MemOpCondition sym)

data MemOpDirection = Read | Write deriving (Bounded, Enum, Eq, Ord, Read, Show)

data MemOp sym ptrW where
  MemOp ::
    -- The address of the operation
    LLVMPtr sym ptrW ->
    MemOpDirection ->
    MemOpCondition sym ->
    -- The size of the operation in bits
    NatRepr w ->
    -- The value read or written during the operation
    LLVMPtr sym w ->
    Endianness ->
    MemOp sym ptrW
  MergeOps ::
    Pred sym ->
    MemTraceImpl sym ptrW ->
    MemTraceImpl sym ptrW ->
    MemOp sym ptrW

instance Eq (MemOpCondition (ExprBuilder t st)) where
  Unconditional == Unconditional = True
  Conditional p == Conditional p' = p == p'
  _ == _ = False

instance Eq (MemOp (ExprBuilder t st) ptrW) where
  MemOp (LLVMPointer addrR addrO) dir cond repr (LLVMPointer valR valO) end
    == MemOp (LLVMPointer addrR' addrO') dir' cond' repr' (LLVMPointer valR' valO') end' = case testEquality repr repr' of
      Nothing -> False
      Just Refl -> addrR == addrR' && addrO == addrO' && dir == dir' && cond == cond' && valR == valR' && valO == valO' && end == end'
  MergeOps p opsT opsF == MergeOps p' opsT' opsF' = p == p' && opsT == opsT' && opsF == opsF'
  _ == _ = False

type MemTraceImpl sym ptrW = Seq (MemOp sym ptrW)
type MemTrace arch = IntrinsicType "memory_trace" (EmptyCtx ::> BVType (ArchAddrWidth arch))

memTraceRepr :: (KnownNat (ArchAddrWidth arch), 1 <= ArchAddrWidth arch) => TypeRepr (MemTrace arch)
memTraceRepr = knownRepr

mkMemTraceVar ::
  forall arch.
  (KnownNat (ArchAddrWidth arch), 1 <= ArchAddrWidth arch) =>
  HandleAllocator ->
  IO (GlobalVar (MemTrace arch))
mkMemTraceVar ha = freshGlobalVar ha (pack "llvm_memory_trace") knownRepr

instance IntrinsicClass (ExprBuilder t st) "memory_trace" where
  -- TODO: cover other cases with a TypeError
  type Intrinsic (ExprBuilder t st) "memory_trace" (EmptyCtx ::> BVType ptrW) = MemTraceImpl (ExprBuilder t st) ptrW
  muxIntrinsic _ _ _ (Empty :> BVRepr _) p l r = pure $ case Seq.spanl (uncurry (==)) (Seq.zip l r) of
    (_, Seq.Empty) -> l
    (eqs, Seq.unzip -> (l', r')) -> (fst <$> eqs) Seq.:|> MergeOps p l' r'
  muxIntrinsic _ _ _ _ _ _ _ = error "Unexpected operands in memory_trace mux"

memTraceIntrinsicTypes :: IsSymInterface (ExprBuilder t st) => IntrinsicTypes (ExprBuilder t st)
memTraceIntrinsicTypes = id
  . MapF.insert (knownSymbol :: SymbolRepr "memory_trace") IntrinsicMuxFn
  . MapF.insert (knownSymbol :: SymbolRepr "LLVM_pointer") IntrinsicMuxFn
  $ MapF.empty

type MacawTraceEvalStmtFunc sym arch = EvalStmtFunc (MacawStmtExtension arch) (MacawSimulatorState sym) sym (MacawExt arch)

execMacawStmtExtension ::
  forall sym arch t st. (IsSymInterface sym, KnownNat (ArchAddrWidth arch), sym ~ ExprBuilder t st) =>
  MacawArchEvalFn sym (MemTrace arch) arch ->
  GlobalVar (MemTrace arch) ->
  GlobalMap sym (MemTrace arch) (ArchAddrWidth arch) ->
  MacawTraceEvalStmtFunc sym arch
execMacawStmtExtension (MacawArchEvalFn archStmtFn) mvar globs stmt
  = case stmt of
    MacawReadMem addrWidth memRepr addr
      -> liftToCrucibleState mvar $ \sym ->
        doReadMem sym addrWidth (regValue addr) memRepr

    MacawCondReadMem addrWidth memRepr cond addr def
      -> liftToCrucibleState mvar $ \sym ->
        doCondReadMem sym (regValue cond) (regValue def) addrWidth (regValue addr) memRepr

    MacawWriteMem addrWidth memRepr addr val
      -> liftToCrucibleState mvar $ \sym ->
        doWriteMem sym addrWidth (regValue addr) (regValue val) memRepr

    MacawCondWriteMem addrWidth memRepr cond addr def
      -> liftToCrucibleState mvar $ \sym ->
        doCondWriteMem sym (regValue cond) addrWidth (regValue addr) (regValue def) memRepr

    MacawGlobalPtr w addr -> \cst -> addrWidthClass w $ doGetGlobal cst mvar globs addr
    MacawFreshSymbolic _t -> error "MacawFreshSymbolic is unsupported in the trace memory model"
    MacawLookupFunctionHandle _typeReps _registers -> error "MacawLookupFunctionHandle is unsupported in the trace memory model"

    MacawArchStmtExtension archStmt -> archStmtFn mvar globs archStmt

    MacawArchStateUpdate{} -> \cst -> pure ((), cst)
    MacawInstructionStart{} -> \cst -> pure ((), cst)

    PtrEq w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      regEq <- natEq sym reg reg'
      offEq <- bvEq sym off off'
      andPred sym regEq offEq

    PtrLeq w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      whoKnows <- ioFreshConstant sym "PtrLeq_across_allocations" knownRepr
      regEq <- natEq sym reg reg'
      offLeq <- bvUle sym off off'
      itePred sym regEq offLeq whoKnows

    PtrLt w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      whoKnows <- ioFreshConstant sym "PtrLt_across_allocations" knownRepr
      regEq <- natEq sym reg reg'
      offLt <- bvUlt sym off off'
      itePred sym regEq offLt whoKnows

    PtrMux w (RegEntry _ p) x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      reg'' <- natIte sym p reg reg'
      off'' <- bvIte sym p off off'
      pure (LLVMPointer reg'' off'')

    PtrAdd w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      regZero <- isZero sym reg
      regZero' <- isZero sym reg'
      someZero <- orPred sym regZero regZero'
      assert sym someZero $ AssertFailureSimError
        "PtrAdd: expected ptr+constant, saw ptr+ptr"
        "When doing pointer addition, we expect at least one of the two arguments to the addition to have a region of 0 (i.e. not be the result of allocating memory). Both arguments had non-0 regions."

      reg'' <- cases sym
        [ (pure regZero, pure reg')
        , (pure regZero', pure reg)
        ]
        (ioFreshConstant sym "PtrAdd_both_ptrs_region" knownRepr)
      off'' <- cases sym
        [ (pure someZero, bvAdd sym off off')
        ]
        (ioFreshConstant sym "PtrAdd_both_ptrs_offset" knownRepr)
      pure (LLVMPointer reg'' off'')

    PtrSub w x y -> ptrOp w x y $ \sym reg off reg' off' -> do
      regZero' <- isZero sym reg'
      regEq <- natEq sym reg reg'
      compatSub <- orPred sym regZero' regEq
      assert sym compatSub $ AssertFailureSimError
        "PtrSub: strange mix of allocation regions"
        "When doing pointer subtraction, we expect that either the two pointers are from the same allocation region or the negated one is actually a constant. Other mixings of allocation regions have arbitrary behavior."

      reg'' <- cases sym
        [ (pure regZero', pure reg)
        , (pure regEq, natLit sym 0)
        ]
        (ioFreshConstant sym "PtrSub_region_mismatch" knownRepr)
      off'' <- cases sym
        [ (pure compatSub, bvSub sym off off')
        ]
        (ioFreshConstant sym "PtrSub_region_mismatch" knownRepr)
      pure (LLVMPointer reg'' off'')

    PtrAnd w x y -> ptrOp w x y $ \sym reg _off reg' _off' -> do
      -- TODO: assertions, like in PtrAdd and PtrSub
      reg'' <- cases sym
        [ (isZero sym reg, pure reg')
        , (isZero sym reg', pure reg)
        , (natEq sym reg reg', pure reg)
        ]
        (ioFreshConstant sym "PtrAnd_across_allocations_region" knownRepr)
      off'' <- cases sym
        undefined
        undefined
      pure (LLVMPointer reg'' off'')

liftToCrucibleState ::
  GlobalVar mem ->
  (sym -> StateT (RegValue sym mem) IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
liftToCrucibleState mvar f cst = do
  mem <- getGlobalVar cst mvar
  (a, mem') <- runStateT (f (cst ^. stateSymInterface)) mem
  pure (a, setGlobalVar cst mvar mem')

readOnlyWithSym ::
  (sym -> IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
readOnlyWithSym f cst = flip (,) cst <$> f (cst ^. stateSymInterface)

getGlobalVar :: CrucibleState s sym ext rtp blocks r ctx -> GlobalVar mem -> IO (RegValue sym mem)
getGlobalVar cst gv = case lookupGlobal gv (cst ^. stateTree . actFrame . gpGlobals) of
  Just val -> return val
  Nothing -> fail ("Global variable not initialized: " ++ show gv)

setGlobalVar :: CrucibleState s sym ext rtp blocks r ctx -> GlobalVar mem -> RegValue sym mem -> CrucibleState s sym ext rtp blocks r ctx
setGlobalVar cst gv val = cst & stateTree . actFrame . gpGlobals %~ insertGlobal gv val

ptrOp ::
  AddrWidthRepr w ->
  RegEntry sym (LLVMPointerType w) ->
  RegEntry sym (LLVMPointerType w) ->
  (1 <= w => sym -> SymNat sym -> SymBV sym w -> SymNat sym -> SymBV sym w -> IO a) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  IO (a, CrucibleState p sym ext rtp blocks r ctx)
ptrOp w (RegEntry _ (LLVMPointer region offset)) (RegEntry _ (LLVMPointer region' offset')) f =
  addrWidthsArePositive w $ readOnlyWithSym $ \sym -> f sym region offset region' offset'

cases ::
  IsExprBuilder sym =>
  sym ->
  [(IO (Pred sym), IO (SymExpr sym tp))] ->
  IO (SymExpr sym tp) ->
  IO (SymExpr sym tp)
cases sym branches def = go branches where
  go [] = def
  go ((iop, iov):bs) = do
    p <- iop
    vT <- iov
    vF <- go bs
    baseTypeIte sym p vT vF

isZero :: IsExprBuilder sym => sym -> SymNat sym -> IO (Pred sym)
isZero sym reg = do
  zero <- natLit sym 0
  natEq sym reg zero

andIOPred :: IsExprBuilder sym => sym -> IO (Pred sym) -> IO (Pred sym) -> IO (Pred sym)
andIOPred sym p1_ p2_ = do
  p1 <- p1_
  p2 <- p2_
  andPred sym p1 p2

orIOPred :: IsExprBuilder sym => sym -> IO (Pred sym) -> IO (Pred sym) -> IO (Pred sym)
orIOPred sym p1_ p2_ = do
  p1 <- p1_
  p2 <- p2_
  orPred sym p1 p2

doReadMem ::
  IsSymInterface sym =>
  sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO (RegValue sym (ToCrucibleType ty))
doReadMem sym ptrWidth ptr memRepr = do
  val <- liftIO $ freshRegValue sym ptr memRepr
  doMemOpInternal sym Read Unconditional ptrWidth ptr val memRepr
  pure val

doCondReadMem ::
  IsSymInterface sym =>
  sym ->
  RegValue sym BoolType ->
  RegValue sym (ToCrucibleType ty) ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO (RegValue sym (ToCrucibleType ty))
doCondReadMem sym cond def ptrWidth ptr memRepr = do
  val <- liftIO $ freshRegValue sym ptr memRepr
  doMemOpInternal sym Read (Conditional cond) ptrWidth ptr val memRepr
  liftIO $ iteDeep sym cond val def memRepr

doWriteMem ::
  IsSymInterface sym =>
  sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doWriteMem sym = doMemOpInternal sym Write Unconditional

doCondWriteMem ::
  IsSymInterface sym =>
  sym ->
  RegValue sym BoolType ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doCondWriteMem sym cond = doMemOpInternal sym Write (Conditional cond)

freshRegValue :: forall sym ptrW ty.
  IsSymInterface sym =>
  sym ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  IO (RegValue sym (ToCrucibleType ty))
freshRegValue sym (LLVMPointer reg off) = go 0 where
  go :: Integer -> MemRepr ty' -> IO (RegValue sym (ToCrucibleType ty'))
  go n (BVMemRepr byteWidth _endianness) = do
    let bitWidth = natMultiply (knownNat @8) byteWidth
    content <- multiplicationIsMonotonic @8 bitWidth $ ioFreshConstant sym
      (intercalate "_" $ describe byteWidth n)
      (BaseBVRepr bitWidth)
    llvmPointer_bv sym content

  go _n (FloatMemRepr _infoRepr _endianness) = fail "creating fresh float values not supported in freshRegValue"

  go n (PackedVecMemRepr countRepr recRepr) = V.generateM (fromInteger (intValue countRepr)) $ \i ->
    go (n + memReprByteSize recRepr * fromIntegral i) recRepr

  describe :: NatRepr w -> Integer -> [String]
  describe = case (asConcrete reg, asConcrete off) of
    (Just (ConcreteNat regVal), Just (ConcreteBV _ offVal)) -> \byteWidth n ->
      ["read", show (natValue byteWidth), show regVal, "0x" ++ showHex (BV.asUnsigned offVal + n) ""]
    _ -> \byteWidth _n -> ["read", show (natValue byteWidth), "symbolic_location"]

doMemOpInternal :: forall sym ptrW ty.
  IsSymInterface sym =>
  sym ->
  MemOpDirection ->
  MemOpCondition sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemTraceImpl sym ptrW) IO ()
doMemOpInternal sym dir cond ptrWidth = go where
  go :: LLVMPtr sym ptrW -> RegValue sym (ToCrucibleType ty') -> MemRepr ty' -> StateT (MemTraceImpl sym ptrW) IO ()
  go ptr@(LLVMPointer reg off) regVal = \case
    BVMemRepr byteWidth endianness -> logOp $ MemOp ptr dir cond bitWidth regVal endianness
      where bitWidth = natMultiply (knownNat @8) byteWidth
    FloatMemRepr _infoRepr _endianness -> fail "reading floats not supported in doMemOpInternal"
    PackedVecMemRepr _countRepr recRepr -> addrWidthsArePositive ptrWidth $ do
      elemSize <- liftIO $ bvLit sym ptrWidthNatRepr (BV.mkBV ptrWidthNatRepr (memReprByteSize recRepr))
      flip V.imapM_ regVal $ \i recRegVal -> do
        off' <- liftIO $ do
          symbolicI <- bvLit sym ptrWidthNatRepr (BV.mkBV ptrWidthNatRepr (toInteger i))
          dOff <- bvMul sym symbolicI elemSize
          bvAdd sym off dOff
        go (LLVMPointer reg off') recRegVal recRepr

  ptrWidthNatRepr = addrWidthNatRepr ptrWidth

iteDeep ::
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  RegValue sym (ToCrucibleType ty) ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  IO (RegValue sym (ToCrucibleType ty))
iteDeep sym cond t f = \case
  BVMemRepr byteWidth _endianness -> let
    bitWidth = natMultiply (knownNat @8) byteWidth
    LLVMPointer treg toff = t
    LLVMPointer freg foff = f
    in multiplicationIsMonotonic @8 bitWidth
    $ liftA2 LLVMPointer (natIte sym cond treg freg) (bvIte sym cond toff foff)
  FloatMemRepr _infoRepr _endianness -> fail "ite on floats not supported in iteDeep"
  PackedVecMemRepr countRepr recRepr -> V.generateM (fromInteger (intValue countRepr)) $ \i ->
    iteDeep sym cond (t V.! i) (f V.! i) recRepr

logOp :: (MonadState (MemTraceImpl sym ptrW) m) => MemOp sym ptrW -> m ()
logOp op = modify (Seq.:|> op)

addrWidthsArePositive :: AddrWidthRepr w -> (1 <= w => a) -> a
addrWidthsArePositive Addr32 a = a
addrWidthsArePositive Addr64 a = a

multiplicationIsMonotonic :: forall x w a. (1 <= x, 1 <= w) => NatRepr (x*w) -> (1 <= x*w => a) -> a
multiplicationIsMonotonic xw a = case compareNat (knownNat @0) xw of
  NatLT _ -> a
  _ -> error $ "The impossible happened: 1 <= x and 1 <= w, but x*w = " ++ show (natValue xw) ++ " and 1 > x*w"

memReprByteSize :: MemRepr ty -> Integer
memReprByteSize (BVMemRepr byteWidth _) = intValue byteWidth
memReprByteSize (FloatMemRepr _ _) = error "byte size of floats not supported in memReprByteSize"
memReprByteSize (PackedVecMemRepr countRepr recRepr) = intValue countRepr * memReprByteSize recRepr

ioSolverSymbol :: String -> IO SolverSymbol
ioSolverSymbol = either (fail . show) pure . userSymbol

ioFreshConstant :: IsSymExprBuilder sym => sym -> String -> BaseTypeRepr tp -> IO (SymExpr sym tp)
ioFreshConstant sym nm ty = do
  symbol <- ioSolverSymbol nm
  freshConstant sym symbol ty
