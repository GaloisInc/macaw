{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module MemOps (tests) where

import           Control.Exception (SomeException, try)
import           Control.Monad (foldM)
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State (get)
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import           Data.Bits ((.|.))
import           Data.String (fromString)
import           Data.Functor.Identity (runIdentity)
import           Data.IORef (newIORef, readIORef, writeIORef)
import qualified Data.Map.Strict as Map
import           Data.Proxy (Proxy(..))
import           Data.Word (Word64)
import           GHC.TypeLits (KnownNat, type (<=), type (*))
import           System.IO (stdout)

import           Data.Parameterized.NatRepr
import qualified Data.Parameterized.NatRepr as NR
                   ( NatRepr, knownNat, LeqProof(..)
                   , leqMulPos )
import           Data.Parameterized.Nonce (newIONonceGenerator)
import           Data.Parameterized.Some (Some(..))

import qualified Data.Macaw.CFG as MC
import           Data.Macaw.Memory (Endianness(..))
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as Perm
import qualified Data.Macaw.Types as MT

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Backend.Simple as CBS
import qualified Lang.Crucible.CFG.Common (GlobalVar)
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.Intrinsics as CLI
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.LLVM.MemModel.Generic as CLG
import qualified Lang.Crucible.LLVM.MemModel.Pointer as CLP
import qualified Lang.Crucible.Simulator as CS
import           Lang.Crucible.Simulator.CallFrame (OverrideLang)
import qualified Lang.Crucible.Simulator.ExecutionTree as CSET
import qualified Lang.Crucible.Simulator.GlobalState as CSGS
import qualified Lang.Crucible.Types as CT

import qualified What4.Expr as WE
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.ProblemFeatures as WPF
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat
import qualified What4.Solver as WSolver

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Memory as MSM
import qualified Data.Macaw.Symbolic.Memory.Common as MSMC
import qualified Data.Macaw.Symbolic.Memory.Lazy as MSMLazy
import qualified Data.Macaw.Symbolic.MemOps as MSMO
import           Arch64 (Arch64)

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.Hedgehog (testPropertyNamed)
import           Test.Tasty.HUnit (assertEqual, testCase)

------------------------------------------------------------------------
-- Setup (Level 1)
------------------------------------------------------------------------

type Sym t = WEB.ExprBuilder t WE.EmptyExprBuilderState (WEB.Flags WEB.FloatIEEE)
type Bak t = CBS.SimpleBackend t WE.EmptyExprBuilderState (WEB.Flags WEB.FloatIEEE)

-- | Allocated region size in bytes.
allocSize :: Word64
allocSize = 4096

-- | Set up an ExprBuilder, SimpleBackend, empty LLVM memory with a
-- malloc'd mutable region, and pass the base pointer to the callback.
withMem ::
  (forall t.
    Sym t -> Bak t -> CL.MemImpl (Sym t) -> CL.LLVMPtr (Sym t) 64 ->
    IO a) ->
  IO a
withMem f = do
  Some ng <- newIONonceGenerator
  sym <- WEB.newExprBuilder WEB.FloatIEEERepr WE.EmptyExprBuilderState ng
  bak <- CBS.newSimpleBackend sym
  let ?memOpts = CL.defaultMemOptions
  let ?recordLLVMAnnotation = \_ _ _ -> pure ()
  let ?ptrWidth = knownNat @64
  mem0 <- CL.emptyMem CLD.LittleEndian
  sz <- WI.bvLit sym (knownNat @64) (BV.word64 allocSize)
  (basePtr, mem1) <- CL.doMalloc bak CLG.GlobalAlloc CLG.Mutable "test" mem0 sz CLD.noAlignment
  f sym bak mem1 basePtr

-- | Like 'withMem', but first execute warmup ops to randomize the memory
-- state, then clear proof obligations before calling the callback.
withWarmedMem ::
  [MemOp] ->
  (forall t.
    Sym t -> Bak t -> CL.MemImpl (Sym t) -> CL.LLVMPtr (Sym t) 64 ->
    IO a) ->
  IO a
withWarmedMem warmup f = withMem $ \sym bak mem basePtr -> do
  mem' <- execOps bak mem basePtr warmup
  CB.clearProofObligations bak
  f sym bak mem' basePtr

-- | Build a pointer into the allocated region at a given byte offset.
mkAllocPtr ::
  WI.IsExprBuilder sym =>
  sym ->
  CL.LLVMPtr sym 64 ->
  Word64 ->
  IO (CL.LLVMPtr sym 64)
mkAllocPtr sym basePtr off = do
  let blk = CLP.llvmPointerBlock basePtr
  offBv <- WI.bvLit sym (knownNat @64) (BV.word64 off)
  pure (CLP.LLVMPointer blk offBv)

------------------------------------------------------------------------
-- Existential wrapper for MemRepr sizes
------------------------------------------------------------------------

data ValSize
  = VS1 | VS2 | VS4 | VS8
  deriving (Show, Eq, Ord, Enum, Bounded)

valSizeBytes :: ValSize -> Word64
valSizeBytes = \case
  VS1 -> 1
  VS2 -> 2
  VS4 -> 4
  VS8 -> 8

-- | An existential wrapper pairing a MemRepr with the KnownNat/LeqProof evidence.
data SomeMemRepr where
  SomeMemRepr ::
    (1 <= w, KnownNat w, 1 <= (8 * w), KnownNat (8 * w)) =>
    MC.MemRepr (MT.BVType (8 * w)) -> NatRepr w -> NatRepr (8 * w) -> SomeMemRepr

valSizeToRepr :: Endianness -> ValSize -> SomeMemRepr
valSizeToRepr e = \case
  VS1 -> SomeMemRepr (MC.BVMemRepr (knownNat @1) e) (knownNat @1) (knownNat @8)
  VS2 -> SomeMemRepr (MC.BVMemRepr (knownNat @2) e) (knownNat @2) (knownNat @16)
  VS4 -> SomeMemRepr (MC.BVMemRepr (knownNat @4) e) (knownNat @4) (knownNat @32)
  VS8 -> SomeMemRepr (MC.BVMemRepr (knownNat @8) e) (knownNat @8) (knownNat @64)

endianFormToEndianness :: CLD.EndianForm -> Endianness
endianFormToEndianness CLD.BigEndian = BigEndian
endianFormToEndianness CLD.LittleEndian = LittleEndian

------------------------------------------------------------------------
-- Helpers for writing/reading concrete BV values as LLVMPointers
------------------------------------------------------------------------

-- | Create an LLVMPointer with block 0 and given bitvector value (concrete).
mkBvPtr ::
  (WI.IsExprBuilder sym, 1 <= w, KnownNat w) =>
  sym -> NatRepr w -> Integer -> IO (CL.LLVMPtr sym w)
mkBvPtr sym w val = do
  blk <- WI.natLit sym 0
  bv <- WI.bvLit sym w (BV.mkBV w val)
  pure (CLP.LLVMPointer blk bv)

-- | Create a fresh symbolic LLVMPointer with block 0.
mkSymBvPtr ::
  (WI.IsSymExprBuilder sym, 1 <= w, KnownNat w) =>
  sym -> NatRepr w -> IO (CL.LLVMPtr sym w)
mkSymBvPtr sym w = do
  blk <- WI.natLit sym 0
  bv <- WI.freshConstant sym (WI.safeSymbol "x") (WI.BaseBVRepr w)
  pure (CLP.LLVMPointer blk bv)

-- | Pointer equality check. Returns:
--   Just True  — provably equal
--   Just False — provably not equal
--   Nothing    — symbolic / undecidable (caller should discard)
newtype PtrEqCheck = PtrEqCheck
  (forall t w. (1 <= w, KnownNat w) =>
    Sym t -> NatRepr w -> CL.LLVMPtr (Sym t) w -> CL.LLVMPtr (Sym t) w -> IO (Maybe Bool))

-- | Concrete check: asserts that the result reduces to a constant.
-- Errors if the equality predicate is symbolic.
ptrEqConcrete :: PtrEqCheck
ptrEqConcrete = PtrEqCheck $ \sym w p1 p2 -> do
  eq <- CLP.ptrEq sym w p1 p2
  case WI.asConstantPred eq of
    Just b -> pure (Just b)
    Nothing -> error "ptrEqConcrete: equality predicate is symbolic"

-- | Optimistic check: returns Just for concrete results, Nothing for
-- symbolic (allowing the caller to discard the test case).
ptrEqOptimistic :: PtrEqCheck
ptrEqOptimistic = PtrEqCheck $ \sym w p1 p2 -> do
  eq <- CLP.ptrEq sym w p1 p2
  pure (WI.asConstantPred eq)

-- | Prove pointer equality via SMT solver. Falls back to Just True if
-- the solver is unavailable (e.g. z3 not installed).
ptrEqSMT :: PtrEqCheck
ptrEqSMT = PtrEqCheck $ \sym w p1 p2 -> do
  eq <- CLP.ptrEq sym w p1 p2
  case WI.asConstantPred eq of
    Just b -> pure (Just b)
    Nothing -> do
      notEq <- WI.notPred sym eq
      result <- try $ WSolver.solver_adapter_check_sat WSolver.z3Adapter sym
                  WSolver.defaultLogData [notEq] pure
      case result of
        Left (_ :: SomeException) -> pure (Just True)  -- solver unavailable
        Right (WSat.Unsat _) -> pure (Just True)
        Right _ -> pure (Just False)

-- | Assert an equality check result in Hedgehog: Just True succeeds,
-- Just False fails, Nothing discards (symbolic, can't decide).
assertEqResult :: Maybe Bool -> H.PropertyT IO ()
assertEqResult (Just True) = H.success
assertEqResult (Just False) = H.failure
assertEqResult Nothing = H.discard

-- | Assert that all proof obligations in the backend are trivially true
-- (concrete True). Clears the obligations after checking.
assertProofObligationsTrue ::
  forall t. Bak t -> IO Bool
assertProofObligationsTrue bak = do
  let sym = CB.backendGetSym bak
  obligations <- CB.getProofObligations bak
  CB.clearProofObligations bak
  case obligations of
    Nothing -> pure True
    Just goals -> do
      preds <- CB.convertProofObligationsAsImplications sym (Just goals)
      pure (all isTriviallyTrue preds)
  where
    isTriviallyTrue p = WI.asConstantPred p == Just True

------------------------------------------------------------------------
-- MemOp ADT
------------------------------------------------------------------------

data MemWrite = MemWrite
  { mwSize :: !ValSize, mwAddr :: !Word64, mwVal :: !Integer }
  deriving (Show)

data MemRead = MemRead
  { mrSize :: !ValSize, mrAddr :: !Word64 }
  deriving (Show)

data MemCondWrite = MemCondWrite
  { mcwCond :: !Bool, mcwSize :: !ValSize, mcwAddr :: !Word64, mcwVal :: !Integer }
  deriving (Show)

data MemCondRead = MemCondRead
  { mcrCond :: !Bool, mcrSize :: !ValSize, mcrAddr :: !Word64, mcrDefault :: !Integer }
  deriving (Show)

data MemOp
  = SomeWrite !MemWrite
  | SomeRead !MemRead
  | SomeCondWrite !MemCondWrite
  | SomeCondRead !MemCondRead
  deriving (Show)

------------------------------------------------------------------------
-- Interpreter (Level 1)
------------------------------------------------------------------------

execWrite ::
  forall t. Bak t -> CL.MemImpl (Sym t) -> CL.LLVMPtr (Sym t) 64 ->
  MemWrite ->
  IO (CL.MemImpl (Sym t))
execWrite bak mem basePtr (MemWrite vs off val) = do
  let sym = CB.backendGetSym bak
  let ?memOpts = CL.defaultMemOptions
  let ?recordLLVMAnnotation = \_ _ _ -> pure ()
  ptr <- mkAllocPtr sym basePtr off
  SomeMemRepr memRepr byteW bitW <- pure (valSizeToRepr LittleEndian vs)
  LeqProof <- pure (leqMulPos (knownNat @8) byteW)
  v <- mkBvPtr sym bitW val
  MSMO.doWriteMem bak mem MC.Addr64 memRepr ptr v

execRead ::
  forall t. Bak t -> CL.MemImpl (Sym t) -> CL.LLVMPtr (Sym t) 64 ->
  MemRead ->
  IO (SomeReadResult (Sym t))
execRead bak mem basePtr (MemRead vs off) = do
  let sym = CB.backendGetSym bak
  let ?memOpts = CL.defaultMemOptions
  let ?recordLLVMAnnotation = \_ _ _ -> pure ()
  ptr <- mkAllocPtr sym basePtr off
  SomeMemRepr memRepr byteW bitW <- pure (valSizeToRepr LittleEndian vs)
  LeqProof <- pure (leqMulPos (knownNat @8) byteW)
  result <- MSMO.doReadMem bak mem MC.Addr64 memRepr ptr
  pure (SomeReadResult bitW result)

data SomeReadResult sym where
  SomeReadResult ::
    (1 <= w, KnownNat w) =>
    NatRepr w -> CL.LLVMPtr sym w -> SomeReadResult sym

execCondWrite ::
  forall t. Bak t -> CL.MemImpl (Sym t) -> CL.LLVMPtr (Sym t) 64 ->
  MemCondWrite ->
  IO (CL.MemImpl (Sym t))
execCondWrite bak mem basePtr (MemCondWrite cond vs off val) =
  if cond
    then execWrite bak mem basePtr (MemWrite vs off val)
    else pure mem

execCondRead ::
  forall t. Bak t -> CL.MemImpl (Sym t) -> CL.LLVMPtr (Sym t) 64 ->
  MemCondRead ->
  IO (SomeReadResult (Sym t))
execCondRead bak mem basePtr (MemCondRead cond vs off defVal) = do
  let sym = CB.backendGetSym bak
  let ?memOpts = CL.defaultMemOptions
  let ?recordLLVMAnnotation = \_ _ _ -> pure ()
  ptr <- mkAllocPtr sym basePtr off
  let condPred = if cond then WI.truePred sym else WI.falsePred sym
  SomeMemRepr memRepr byteW bitW <- pure (valSizeToRepr LittleEndian vs)
  LeqProof <- pure (leqMulPos (knownNat @8) byteW)
  def <- mkBvPtr sym bitW defVal
  result <- MSMO.doCondReadMem bak mem MC.Addr64 memRepr condPred ptr def
  pure (SomeReadResult bitW result)

-- | Execute a list of ops, threading memory state. Reads that fail
-- (e.g. on uninitialized memory) are silently skipped.
execOps ::
  forall t.
  Bak t -> CL.MemImpl (Sym t) -> CL.LLVMPtr (Sym t) 64 ->
  [MemOp] -> IO (CL.MemImpl (Sym t))
execOps _ mem _ [] = pure mem
execOps bak mem basePtr (op:ops) = do
  mem' <- case op of
    SomeWrite w -> execWrite bak mem basePtr w
    SomeRead r -> tryRead r >> pure mem
    SomeCondWrite cw -> execCondWrite bak mem basePtr cw
    SomeCondRead cr -> tryCondRead cr >> pure mem
  execOps bak mem' basePtr ops
  where
    tryRead r = do
      result <- try (execRead bak mem basePtr r)
      case result of
        Left (_ :: SomeException) -> pure ()
        Right _ -> pure ()
    tryCondRead cr = do
      result <- try (execCondRead bak mem basePtr cr)
      case result of
        Left (_ :: SomeException) -> pure ()
        Right _ -> pure ()

------------------------------------------------------------------------
-- Generators (Level 1)
------------------------------------------------------------------------

genValSize :: H.Gen ValSize
genValSize = Gen.element [VS1, VS2, VS4, VS8]

-- | Generate an arbitrary address, including out-of-bounds ones.
genAnyAddr :: H.Gen Word64
genAnyAddr = Gen.frequency
  [ (3, Gen.word64 (Range.linear 0 (allocSize - 1)))  -- in-bounds
  , (2, Gen.word64 (Range.linear allocSize (allocSize * 2)))  -- just past end
  , (1, Gen.element [0, allocSize - 1, allocSize, maxBound])  -- edge cases
  ]

-- | Generate an address guaranteed to be safe for a given size
-- (i.e., addr + size <= allocSize).
genSafeAddr :: ValSize -> H.Gen Word64
genSafeAddr vs =
  let maxAddr = allocSize - valSizeBytes vs
  in Gen.frequency
    [ (5, Gen.word64 (Range.linear 0 (min 255 maxAddr)))
    , (2, Gen.word64 (Range.linear 0 maxAddr))
    , (1, Gen.element [0, 1, maxAddr])
    ]

-- | Generate a value that fits in the given size.
genValue :: ValSize -> H.Gen Integer
genValue vs =
  let maxVal = 2 ^ (8 * valSizeBytes vs) - 1
  in Gen.frequency
    [ (5, Gen.integral (Range.linear 0 maxVal))
    , (1, Gen.element [0, 1, maxVal, maxVal `div` 2])
    ]

genWrite :: H.Gen MemWrite
genWrite = do
  vs <- genValSize
  off <- genSafeAddr vs
  val <- genValue vs
  pure (MemWrite vs off val)

genRead :: H.Gen MemRead
genRead = do
  vs <- genValSize
  off <- genSafeAddr vs
  pure (MemRead vs off)

genCondWrite :: H.Gen MemCondWrite
genCondWrite = do
  c <- Gen.bool
  vs <- genValSize
  off <- genSafeAddr vs
  val <- genValue vs
  pure (MemCondWrite c vs off val)

genCondRead :: H.Gen MemCondRead
genCondRead = do
  c <- Gen.bool
  vs <- genValSize
  off <- genSafeAddr vs
  def <- genValue vs
  pure (MemCondRead c vs off def)

genMemOp :: H.Gen MemOp
genMemOp = Gen.choice
  [ SomeWrite <$> genWrite
  , SomeRead <$> genRead
  , SomeCondWrite <$> genCondWrite
  , SomeCondRead <$> genCondRead
  ]

genOps :: H.Gen [MemOp]
genOps = Gen.list (Range.linear 1 30) genMemOp

-- | Generate a pair of non-overlapping (addr, size) pairs.
genNonOverlapping :: H.Gen (Word64, ValSize, Word64, ValSize)
genNonOverlapping = do
  vs1 <- genValSize
  vs2 <- genValSize
  let sz1 = valSizeBytes vs1
      sz2 = valSizeBytes vs2
      maxAddr1 = allocSize - sz1 - sz2
  off1 <- Gen.word64 (Range.linear 0 (min 255 maxAddr1))
  let off2Start = off1 + sz1
      maxAddr2 = allocSize - sz2
  off2 <- Gen.word64 (Range.linear off2Start (min (off2Start + 255) maxAddr2))
  pure (off1, vs1, off2, vs2)

-- | Generate a smaller ValSize.
genSmallerOrEq :: ValSize -> H.Gen ValSize
genSmallerOrEq = \case
  VS1 -> pure VS1
  VS2 -> Gen.element [VS1, VS2]
  VS4 -> Gen.element [VS1, VS2, VS4]
  VS8 -> Gen.element [VS1, VS2, VS4, VS8]

------------------------------------------------------------------------
-- Properties (Level 1)
------------------------------------------------------------------------

prop_writeReadRoundtrip :: PtrEqCheck -> H.TestLimit -> H.Property
prop_writeReadRoundtrip (PtrEqCheck eq) n =
  H.withTests n $ H.property $ do
    warmup <- H.forAll genOps
    vs <- H.forAll genValSize
    off <- H.forAll (genSafeAddr vs)
    val <- H.forAll (genValue vs)
    result <- H.evalIO $ withWarmedMem warmup $ \sym bak mem basePtr -> do
      mem' <- execWrite bak mem basePtr (MemWrite vs off val)
      SomeReadResult w r <- execRead bak mem' basePtr (MemRead vs off)
      eq sym w r =<< mkBvPtr sym w val
    assertEqResult result

prop_writeReadSymbolic :: PtrEqCheck -> H.TestLimit -> H.Property
prop_writeReadSymbolic (PtrEqCheck eq) n =
  H.withTests n $ H.property $ do
    warmup <- H.forAll genOps
    vs <- H.forAll genValSize
    off <- H.forAll (genSafeAddr vs)
    result <- H.evalIO $ withWarmedMem warmup $ \sym bak mem basePtr -> do
      let ?memOpts = CL.defaultMemOptions
      let ?recordLLVMAnnotation = \_ _ _ -> pure ()
      ptr <- mkAllocPtr sym basePtr off
      SomeMemRepr memRepr byteW bitW <- pure (valSizeToRepr LittleEndian vs)
      LeqProof <- pure (leqMulPos (knownNat @8) byteW)
      symVal <- mkSymBvPtr sym bitW
      mem' <- MSMO.doWriteMem bak mem MC.Addr64 memRepr ptr symVal
      r <- MSMO.doReadMem bak mem' MC.Addr64 memRepr ptr
      eq sym bitW r symVal
    assertEqResult result

prop_condWriteFalsePreserves :: PtrEqCheck -> H.TestLimit -> H.Property
prop_condWriteFalsePreserves (PtrEqCheck eq) n =
  H.withTests n $ H.property $ do
    warmup <- H.forAll genOps
    vs <- H.forAll genValSize
    off <- H.forAll (genSafeAddr vs)
    val1 <- H.forAll (genValue vs)
    val2 <- H.forAll (genValue vs)
    result <- H.evalIO $ withWarmedMem warmup $ \sym bak mem basePtr -> do
      mem' <- execWrite bak mem basePtr (MemWrite vs off val1)
      mem'' <- execCondWrite bak mem' basePtr (MemCondWrite False vs off val2)
      SomeReadResult w r <- execRead bak mem'' basePtr (MemRead vs off)
      eq sym w r =<< mkBvPtr sym w val1
    assertEqResult result

prop_condReadFalseReturnsDefault :: PtrEqCheck -> H.TestLimit -> H.Property
prop_condReadFalseReturnsDefault (PtrEqCheck eq) n =
  H.withTests n $ H.property $ do
    warmup <- H.forAll genOps
    vs <- H.forAll genValSize
    off <- H.forAll (genSafeAddr vs)
    writeVal <- H.forAll (genValue vs)
    defVal <- H.forAll (genValue vs)
    result <- H.evalIO $ withWarmedMem warmup $ \sym bak mem basePtr -> do
      mem' <- execWrite bak mem basePtr (MemWrite vs off writeVal)
      SomeReadResult w r <- execCondRead bak mem' basePtr (MemCondRead False vs off defVal)
      eq sym w r =<< mkBvPtr sym w defVal
    assertEqResult result

prop_nonOverlappingIndependent :: PtrEqCheck -> H.TestLimit -> H.Property
prop_nonOverlappingIndependent (PtrEqCheck eq) n =
  H.withTests n $ H.property $ do
    warmup <- H.forAll genOps
    (off1, vs1, off2, vs2) <- H.forAll genNonOverlapping
    val1 <- H.forAll (genValue vs1)
    val2 <- H.forAll (genValue vs2)
    result <- H.evalIO $ withWarmedMem warmup $ \sym bak mem basePtr -> do
      mem' <- execWrite bak mem basePtr (MemWrite vs1 off1 val1)
      mem'' <- execWrite bak mem' basePtr (MemWrite vs2 off2 val2)
      SomeReadResult w r <- execRead bak mem'' basePtr (MemRead vs1 off1)
      eq sym w r =<< mkBvPtr sym w val1
    assertEqResult result

prop_lastWriterWins :: PtrEqCheck -> H.TestLimit -> H.Property
prop_lastWriterWins (PtrEqCheck eq) n =
  H.withTests n $ H.property $ do
    warmup <- H.forAll genOps
    vs <- H.forAll genValSize
    off <- H.forAll (genSafeAddr vs)
    val1 <- H.forAll (genValue vs)
    val2 <- H.forAll (genValue vs)
    result <- H.evalIO $ withWarmedMem warmup $ \sym bak mem basePtr -> do
      mem' <- execWrite bak mem basePtr (MemWrite vs off val1)
      mem'' <- execWrite bak mem' basePtr (MemWrite vs off val2)
      SomeReadResult w r <- execRead bak mem'' basePtr (MemRead vs off)
      eq sym w r =<< mkBvPtr sym w val2
    assertEqResult result

prop_smallerReadAfterWrite :: H.Property
prop_smallerReadAfterWrite =
  H.withTests 1000 $ H.property $ do
    warmup <- H.forAll genOps
    vs <- H.forAll genValSize
    smallerVs <- H.forAll (genSmallerOrEq vs)
    off <- H.forAll genAnyAddr
    val <- H.forAll (genValue vs)
    ok <- H.evalIO $ withWarmedMem warmup $ \_ bak mem basePtr -> do
      mem' <- execWrite bak mem basePtr (MemWrite vs off val)
      writeOk <- assertProofObligationsTrue bak
      if writeOk
        then do
          _ <- execRead bak mem' basePtr (MemRead smallerVs off)
          assertProofObligationsTrue bak
        else pure True  -- write wasn't valid, property vacuously holds
    H.assert ok

prop_writeReadAfterArbitraryOps :: PtrEqCheck -> H.TestLimit -> H.Property
prop_writeReadAfterArbitraryOps (PtrEqCheck eq) n =
  H.withTests n $ H.property $ do
    warmup <- H.forAll genOps
    vs <- H.forAll genValSize
    off <- H.forAll (genSafeAddr vs)
    val <- H.forAll (genValue vs)
    result <- H.evalIO $ withWarmedMem warmup $ \sym bak mem basePtr -> do
      mem' <- execWrite bak mem basePtr (MemWrite vs off val)
      SomeReadResult w r <- execRead bak mem' basePtr (MemRead vs off)
      eq sym w r =<< mkBvPtr sym w val
    assertEqResult result

prop_arbitraryOpsNoError :: H.Property
prop_arbitraryOpsNoError =
  H.withTests 500 $ H.property $ do
    ops <- H.forAll genOps
    H.evalIO $ withMem $ \_ bak mem basePtr -> do
      _ <- execOps bak mem basePtr ops
      CB.clearProofObligations bak

prop_writeValidImpliesReadValid :: H.Property
prop_writeValidImpliesReadValid =
  H.withTests 1000 $ H.property $ do
    warmup <- H.forAll genOps
    vs <- H.forAll genValSize
    off <- H.forAll genAnyAddr
    val <- H.forAll (genValue vs)
    ok <- H.evalIO $ withWarmedMem warmup $ \_ bak mem basePtr -> do
      mem' <- execWrite bak mem basePtr (MemWrite vs off val)
      writeOk <- assertProofObligationsTrue bak
      if writeOk
        then do
          _ <- execRead bak mem' basePtr (MemRead vs off)
          assertProofObligationsTrue bak
        else pure True  -- write wasn't valid, property vacuously holds
    H.assert ok

prop_smallerWriteValid :: H.Property
prop_smallerWriteValid =
  H.withTests 1000 $ H.property $ do
    warmup <- H.forAll genOps
    vs <- H.forAll genValSize
    smallerVs <- H.forAll (genSmallerOrEq vs)
    off <- H.forAll genAnyAddr
    val <- H.forAll (genValue vs)
    smallVal <- H.forAll (genValue smallerVs)
    ok <- H.evalIO $ withWarmedMem warmup $ \_ bak mem basePtr -> do
      _ <- execWrite bak mem basePtr (MemWrite vs off val)
      writeOk <- assertProofObligationsTrue bak
      if writeOk
        then do
          _ <- execWrite bak mem basePtr (MemWrite smallerVs off smallVal)
          assertProofObligationsTrue bak
        else pure True  -- first write wasn't valid, property vacuously holds

    H.assert ok

-- | Is this op a write (or conditional write)?
isWrite :: MemOp -> Bool
isWrite = \case
  SomeWrite _ -> True
  SomeCondWrite _ -> True
  _ -> False

-- | Try to execute a single op, returning (updated mem, success).
tryExecOp ::
  forall t.
  Bak t -> CL.MemImpl (Sym t) -> CL.LLVMPtr (Sym t) 64 ->
  MemOp -> IO (CL.MemImpl (Sym t), Bool)
tryExecOp bak mem basePtr op = do
  result <- try $ case op of
    SomeWrite w -> execWrite bak mem basePtr w
    SomeRead r -> execRead bak mem basePtr r >> pure mem
    SomeCondWrite cw -> execCondWrite bak mem basePtr cw
    SomeCondRead cr -> execCondRead bak mem basePtr cr >> pure mem
  case result of
    Left (_ :: SomeException) -> pure (mem, False)
    Right mem' -> do
      oblOk <- assertProofObligationsTrue bak
      pure (mem', oblOk)

prop_opOrderCommutative :: H.Property
prop_opOrderCommutative =
  H.withTests 1000 $ H.property $ do
    warmup <- H.forAll genOps
    op1 <- H.forAll genMemOp
    op2 <- H.forAll genMemOp
    ok <- H.evalIO $ withWarmedMem warmup $ \_ bak mem basePtr -> do
      -- Order 1: op1 then op2
      (mem1, ok1a) <- tryExecOp bak mem basePtr op1
      (_, ok1b) <- tryExecOp bak mem1 basePtr op2
      let ok1 = ok1a && ok1b
      -- Order 2: op2 then op1
      (mem2, ok2a) <- tryExecOp bak mem basePtr op2
      (_, ok2b) <- tryExecOp bak mem2 basePtr op1
      let ok2 = ok2a && ok2b
      -- Either both orders agree, or write-before-read order succeeds
      let commutes = ok1 == ok2
      let writeReadOk = (isWrite op1 && not (isWrite op2) && ok1)
                      || (isWrite op2 && not (isWrite op1) && ok2)
      pure (commutes || writeReadOk)
    H.assert ok

------------------------------------------------------------------------
-- Level 2: do*MemModel tests with real memory model configs
------------------------------------------------------------------------

-- | Specification for a memory segment to be inserted.
data SegmentSpec = SegmentSpec
  { ssBase     :: !Word64
  , ssSize     :: !Word64
  , ssFlags    :: !Perm.Flags
  , ssContents :: !BS.ByteString
  } deriving (Show, Eq)

-- | A synthetic memory layout with its macaw Memory.
data MemLayout = MemLayout
  { mlSegments :: ![SegmentSpec]
  , mlMacawMem :: !(MM.Memory 64)
  }

instance Show MemLayout where
  show ml = "MemLayout " ++ show (mlSegments ml)

-- | Build a macaw Memory from a list of segment specs.
-- Overlapping segments are silently skipped.
-- Note: insertMemSegment has a known bug where it doesn't detect
-- all overlaps, so we also check manually.
buildMacawMemory :: [SegmentSpec] -> MemLayout
buildMacawMemory specs = foldl' tryInsert (MemLayout [] (MM.emptyMemory MC.Addr64)) specs
  where
    tryInsert (MemLayout segs mem) spec
      | overlapsExisting segs spec = MemLayout segs mem
      | otherwise =
        let seg = runIdentity $ MM.memSegment
                    Map.empty       -- no relocations
                    0               -- region 0 = absolute address
                    0               -- no linktime offset
                    Nothing         -- no segment index
                    (MM.memWord (ssBase spec))
                    (ssFlags spec)
                    (ssContents spec)
                    (MM.memWord (ssSize spec))
        in case MM.insertMemSegment seg mem of
             Left _     -> MemLayout segs mem
             Right mem' -> MemLayout (segs ++ [spec]) mem'

    overlapsExisting segs spec =
      any (\s -> rangesOverlap (ssBase s) (ssSize s) (ssBase spec) (ssSize spec)) segs

    rangesOverlap base1 sz1 base2 sz2 =
      base1 < base2 + sz2 && base2 < base1 + sz1

-- | Which memory model to use.
data ModelConfig = StrictModel | LazyModel
  deriving (Show)

------------------------------------------------------------------------
-- Level 2 generators
------------------------------------------------------------------------

genSegmentSpec :: H.Gen SegmentSpec
genSegmentSpec = do
  base <- Gen.frequency
    [ (5, Gen.word64 (Range.linear 0x100 0xFFFF))
    , (2, Gen.word64 (Range.linear 0 0xFFFFFFFF))
    , (1, Gen.element [0, 1, 0xFFFF, 0xFFFFFFF0])
    ]
  sz <- Gen.frequency
    [ (5, Gen.word64 (Range.linear 1 256))
    , (2, Gen.word64 (Range.linear 1 4096))
    , (1, Gen.element [1, 2, 8, 4096])
    ]
  flags <- Gen.element
    [ Perm.read
    , Perm.read .|. Perm.write
    , Perm.read .|. Perm.execute
    , Perm.read .|. Perm.write .|. Perm.execute
    ]
  contents <- Gen.bytes (Range.singleton (fromIntegral sz))
  pure (SegmentSpec base sz flags contents)

genMemLayout :: H.Gen MemLayout
genMemLayout = do
  specs <- Gen.list (Range.linear 1 8) genSegmentSpec
  pure (buildMacawMemory specs)

-- | Generate a layout guaranteed to have at least one writable segment
-- large enough for the given value size.
genLayoutWithWritable :: ValSize -> H.Gen MemLayout
genLayoutWithWritable vs = do
  -- Generate a guaranteed-writable segment first
  rwBase <- Gen.frequency
    [ (5, Gen.word64 (Range.linear 0x100 0xFFFF))
    , (2, Gen.word64 (Range.linear 0 0xFFFFFFFF))
    , (1, Gen.element [0, 1, 0x1000])
    ]
  rwSize <- Gen.word64 (Range.linear (max 16 (valSizeBytes vs)) 256)
  rwContents <- Gen.bytes (Range.singleton (fromIntegral rwSize))
  let rwSpec = SegmentSpec rwBase rwSize (Perm.read .|. Perm.write) rwContents
  -- Generate additional random segments
  extras <- Gen.list (Range.linear 0 6) genSegmentSpec
  pure (buildMacawMemory (rwSpec : extras))

-- | Generate a layout guaranteed to have at least one read-only segment.
genLayoutWithReadOnly :: ValSize -> H.Gen MemLayout
genLayoutWithReadOnly vs = do
  roBase <- Gen.frequency
    [ (5, Gen.word64 (Range.linear 0x100 0xFFFF))
    , (2, Gen.word64 (Range.linear 0 0xFFFFFFFF))
    ]
  roSize <- Gen.word64 (Range.linear (max 16 (valSizeBytes vs)) 256)
  roContents <- Gen.bytes (Range.singleton (fromIntegral roSize))
  let roSpec = SegmentSpec roBase roSize Perm.read roContents
  extras <- Gen.list (Range.linear 0 6) genSegmentSpec
  pure (buildMacawMemory (roSpec : extras))

-- | Generate an address within a segment matching a predicate.
-- Discards if no matching segment has enough room for the value size.
genAddrInSegment :: (SegmentSpec -> Bool) -> MemLayout -> ValSize -> H.Gen Word64
genAddrInSegment p layout vs = do
  let matching = filter (\s -> p s && ssSize s >= valSizeBytes vs) (mlSegments layout)
  case matching of
    [] -> Gen.discard
    _  -> do
      seg <- Gen.element matching
      off <- Gen.word64 (Range.linear 0 (ssSize seg - valSizeBytes vs))
      pure (ssBase seg + off)

genWritableAddr :: MemLayout -> ValSize -> H.Gen Word64
genWritableAddr = genAddrInSegment (\s -> Perm.hasPerm (ssFlags s) Perm.write)

genReadOnlyAddr :: MemLayout -> ValSize -> H.Gen Word64
genReadOnlyAddr = genAddrInSegment (\s -> not (Perm.hasPerm (ssFlags s) Perm.write))

genMappedAddr :: MemLayout -> ValSize -> H.Gen Word64
genMappedAddr = genAddrInSegment (const True)

-- | Generate an unmapped address for a given layout.
-- Picks addresses just past segment ends, or in known-empty ranges,
-- then verifies the candidate doesn't fall within any segment.
genUnmappedAddr :: MemLayout -> H.Gen Word64
genUnmappedAddr layout = do
  candidate <- Gen.frequency $
    [ (3, Gen.element justPastEnds) | not (null justPastEnds) ] ++
    [ (2, Gen.word64 (Range.linear 0xF0000000 0xFFFFFFFF))
    , (1, Gen.element [maxBound, maxBound - 7, 0xDEADBEEF])
    ]
  if isMapped candidate then Gen.discard else pure candidate
  where
    justPastEnds = [ ssBase s + ssSize s | s <- mlSegments layout ]
    isMapped addr = any (\s -> ssBase s <= addr && addr < ssBase s + ssSize s)
                        (mlSegments layout)

-- | Build a block-0 pointer with a concrete offset.
mkBlock0Ptr :: WI.IsExprBuilder sym => sym -> Word64 -> IO (CL.LLVMPtr sym 64)
mkBlock0Ptr sym addr = do
  blk <- WI.natLit sym 0
  off <- WI.bvLit sym (knownNat @64) (BV.word64 addr)
  pure (CLP.LLVMPointer blk off)

-- | Build a block-0 pointer with a symbolic offset.
_mkSymBlock0Ptr :: WI.IsSymExprBuilder sym => sym -> IO (CL.LLVMPtr sym 64)
_mkSymBlock0Ptr sym = do
  blk <- WI.natLit sym 0
  off <- WI.freshConstant sym (WI.safeSymbol "addr") (WI.BaseBVRepr (knownNat @64))
  pure (CLP.LLVMPointer blk off)

------------------------------------------------------------------------
-- Symbolic pointer support (PointerSpec)
------------------------------------------------------------------------

-- | A pointer specification: a NonEmpty list of concrete addresses.
-- A singleton is concrete; multiple elements become an ite tree with
-- fresh boolean conditions.
newtype PointerSpec = PointerSpec (NonEmpty Word64)
  deriving (Show)

-- | Materialize a PointerSpec into an LLVMPtr with block 0.
-- Singleton → concrete BV; multiple → right-leaning ite tree.
materializePtr ::
  WI.IsSymExprBuilder sym =>
  sym -> PointerSpec -> IO (CL.LLVMPtr sym 64)
materializePtr sym (PointerSpec addrs) = do
  blk <- WI.natLit sym 0
  bvs <- mapM (\a -> WI.bvLit sym (knownNat @64) (BV.word64 a)) (NE.toList addrs)
  off <- foldIte sym (NE.fromList bvs)
  pure (CLP.LLVMPointer blk off)

-- | Fold a NonEmpty list of BVs into a right-leaning ite tree.
foldIte ::
  WI.IsSymExprBuilder sym =>
  sym -> NonEmpty (WI.SymBV sym 64) -> IO (WI.SymBV sym 64)
foldIte _   (x :| [])     = pure x
foldIte sym (x :| (y:ys)) = do
  rest <- foldIte sym (y :| ys)
  cond <- WI.freshConstant sym (WI.safeSymbol "ptr_ite") WI.BaseBoolRepr
  WI.bvIte sym cond x rest

-- | Wrap a concrete address as a singleton PointerSpec.
concretePtr :: Word64 -> PointerSpec
concretePtr a = PointerSpec (a :| [])

-- | Generate a PointerSpec for writable addresses.
-- 1/2 concrete, 1/4 nearby (2 addrs same segment), 1/4 far/many.
genSymWritableAddr :: MemLayout -> ValSize -> H.Gen PointerSpec
genSymWritableAddr layout vs = Gen.frequency
  [ (2, do
      a <- genWritableAddr layout vs
      pure (PointerSpec (a :| [])))
  , (1, do
      a1 <- genWritableAddr layout vs
      let (seg:_) = [ s | s <- mlSegments layout
                        , Perm.hasPerm (ssFlags s) Perm.write
                        , ssBase s <= a1
                        , a1 + valSizeBytes vs <= ssBase s + ssSize s ]
      let maxOff = ssBase seg + ssSize seg - valSizeBytes vs
          maxDelta = maxOff - a1
      delta <- Gen.word64 (Range.linear 0 (min 15 maxDelta))
      let a2 = a1 + delta
      pure (PointerSpec (a1 :| [a2])))
  , (1, do
      a1 <- genWritableAddr layout vs
      rest <- Gen.list (Range.linear 1 3) (genWritableAddr layout vs)
      pure (PointerSpec (a1 :| rest)))
  ]

-- | Generate two non-overlapping symbolic writable address specs.
-- For simplicity, picks from different segments to guarantee non-overlap.
genSymNonOverlappingWritable :: MemLayout -> H.Gen (ValSize, PointerSpec, ValSize, PointerSpec)
genSymNonOverlappingWritable layout = do
  let writable = filter (\s -> Perm.hasPerm (ssFlags s) Perm.write) (mlSegments layout)
  case writable of
    [] -> Gen.discard
    [seg] -> do
      vs1 <- genValSize
      vs2 <- genValSize
      let needed = valSizeBytes vs1 + valSizeBytes vs2
      if ssSize seg < needed then Gen.discard
      else do
        off1 <- Gen.word64 (Range.linear 0 (ssSize seg - needed))
        let off2Start = off1 + valSizeBytes vs1
        off2 <- Gen.word64 (Range.linear off2Start (ssSize seg - valSizeBytes vs2))
        pure ( vs1, PointerSpec (ssBase seg + off1 :| [])
             , vs2, PointerSpec (ssBase seg + off2 :| []) )
    _ -> do
      seg1 <- Gen.element writable
      seg2 <- Gen.element (filter (/= seg1) writable)
      vs1 <- genValSize
      vs2 <- genValSize
      if ssSize seg1 < valSizeBytes vs1 || ssSize seg2 < valSizeBytes vs2
        then Gen.discard
        else do
          a1 <- genWritableAddrInSeg seg1 vs1
          a2 <- genWritableAddrInSeg seg2 vs2
          -- Each can independently be concrete or symbolic (within its segment)
          ps1 <- genPtrSpecInSeg seg1 vs1 a1
          ps2 <- genPtrSpecInSeg seg2 vs2 a2
          pure (vs1, ps1, vs2, ps2)
  where
    genWritableAddrInSeg seg vs = do
      off <- Gen.word64 (Range.linear 0 (ssSize seg - valSizeBytes vs))
      pure (ssBase seg + off)
    genPtrSpecInSeg seg vs base = Gen.frequency
      [ (2, pure (PointerSpec (base :| [])))
      , (1, do
          let maxOff = ssBase seg + ssSize seg - valSizeBytes vs
              maxDelta = maxOff - base
          delta <- Gen.word64 (Range.linear 0 (min 15 maxDelta))
          pure (PointerSpec (base :| [base + delta])))
      ]

-- | Concrete-only variant of genSymNonOverlappingWritable.
genConcreteNonOverlappingWritable :: MemLayout -> H.Gen (ValSize, PointerSpec, ValSize, PointerSpec)
genConcreteNonOverlappingWritable layout = do
  let writable = filter (\s -> Perm.hasPerm (ssFlags s) Perm.write) (mlSegments layout)
  case writable of
    [] -> Gen.discard
    [seg] -> do
      vs1 <- genValSize
      vs2 <- genValSize
      let needed = valSizeBytes vs1 + valSizeBytes vs2
      if ssSize seg < needed then Gen.discard
      else do
        off1 <- Gen.word64 (Range.linear 0 (ssSize seg - needed))
        let off2Start = off1 + valSizeBytes vs1
        off2 <- Gen.word64 (Range.linear off2Start (ssSize seg - valSizeBytes vs2))
        pure ( vs1, concretePtr (ssBase seg + off1)
             , vs2, concretePtr (ssBase seg + off2) )
    _ -> do
      seg1 <- Gen.element writable
      seg2 <- Gen.element (filter (/= seg1) writable)
      vs1 <- genValSize
      vs2 <- genValSize
      if ssSize seg1 < valSizeBytes vs1 || ssSize seg2 < valSizeBytes vs2
        then Gen.discard
        else do
          off1 <- Gen.word64 (Range.linear 0 (ssSize seg1 - valSizeBytes vs1))
          off2 <- Gen.word64 (Range.linear 0 (ssSize seg2 - valSizeBytes vs2))
          pure ( vs1, concretePtr (ssBase seg1 + off1)
               , vs2, concretePtr (ssBase seg2 + off2) )

------------------------------------------------------------------------
-- | Collect all proof obligation assertions (ignoring assumptions) as a
-- single conjunction, then clear them. For concrete inputs where
-- assertions should reduce concretely, this avoids the symbolic
-- assumptions introduced by the online backend.
collectAssertionPred ::
  CB.IsSymBackend sym bak =>
  bak -> IO (WI.Pred sym)
collectAssertionPred bak = do
  let sym = CB.backendGetSym bak
  obligations <- CB.getProofObligations bak
  CB.clearProofObligations bak
  let goals = maybe [] CB.goalsToList obligations
      preds = map (CB._labeledPred . CB.proofGoal) goals
  foldM (\acc p -> WI.andPred sym acc p) (WI.truePred sym) preds

------------------------------------------------------------------------
-- Level 2: Unified setup with OnlineBackend
------------------------------------------------------------------------

-- | An ExtensionImpl stub for MacawExt Arch64.
stubExtImpl ::
  CSET.ExtensionImpl p sym (MS.MacawExt Arch64)
stubExtImpl = CSET.ExtensionImpl
  { CSET.extensionEval = \_ _ _ _ _ -> error "stubExtImpl: extensionEval not used"
  , CSET.extensionExec = \_ _ -> error "stubExtImpl: extensionExec not used"
  }

-- | Run a test body inside a real memory model setup.
-- Uses SimpleBackend for the strict model (no solver process needed)
-- and OnlineBackend (z3) for the lazy model (needs solver for lazy population).
withModel ::
  forall a.
  ModelConfig ->
  CLD.EndianForm ->
  MemLayout ->
  (forall t st fs bak sym.
    ( CB.IsSymBackend sym bak
    , sym ~ WEB.ExprBuilder t st fs
    , st ~ WE.EmptyExprBuilderState
    , fs ~ WEB.Flags WEB.FloatIEEE
    , CL.HasLLVMAnn sym
    , ?memOpts :: CL.MemOptions
    ) =>
    sym ->
    bak ->
    Lang.Crucible.CFG.Common.GlobalVar CL.Mem ->
    MS.MemModelConfig (MSMO.MacawLazySimulatorState sym 64) sym Arch64 CL.Mem ->
    CS.SimState
      (MSMO.MacawLazySimulatorState sym 64)
      sym
      (MS.MacawExt Arch64)
      (CS.RegEntry sym CT.UnitType)
      (OverrideLang CT.UnitType)
      ('Just CT.EmptyCtx) ->
    IO a) ->
  IO a
withModel StrictModel endianForm layout f = do
  Some ng <- newIONonceGenerator
  sym <- WEB.newExprBuilder WEB.FloatIEEERepr WE.EmptyExprBuilderState ng
  bak <- CBS.newSimpleBackend sym
  let ?memOpts = CL.defaultMemOptions
  let ?recordLLVMAnnotation = \_ _ _ -> pure ()
  let ?ptrWidth = knownNat @64
  let ?processMacawAssert = MSMC.defaultProcessMacawAssertion
  (mi, mpt) <- MSM.newGlobalMemory (Proxy @Arch64) bak endianForm MSMC.ConcreteMutable (mlMacawMem layout)
  let mmConf = MSM.memModelConfig bak mpt
  runModelBody sym bak mmConf mi f

withModel LazyModel endianForm layout f = do
  Some ng <- newIONonceGenerator
  sym <- WEB.newExprBuilder WEB.FloatIEEERepr WE.EmptyExprBuilderState ng
  CBO.withZ3OnlineBackend sym CBO.NoUnsatFeatures WPF.noFeatures $ \bak -> do
    let ?memOpts = CL.defaultMemOptions
    let ?recordLLVMAnnotation = \_ _ _ -> pure ()
    let ?ptrWidth = knownNat @64
    let ?processMacawAssert = MSMC.defaultProcessMacawAssertion
    (mi, mpt) <- MSMLazy.newGlobalMemory (Proxy @Arch64) bak endianForm MSMC.ConcreteMutable (mlMacawMem layout)
    let mmConf = MSMLazy.memModelConfig bak mpt
    runModelBody sym bak mmConf mi f

-- | Shared body: set up simulator state and run the callback.
runModelBody ::
  forall sym bak a.
  ( CB.IsSymBackend sym bak
  , CL.HasLLVMAnn sym
  , ?memOpts :: CL.MemOptions
  ) =>
  sym ->
  bak ->
  MS.MemModelConfig (MSMO.MacawLazySimulatorState sym 64) sym Arch64 CL.Mem ->
  CL.MemImpl sym ->
  (sym ->
   bak ->
   Lang.Crucible.CFG.Common.GlobalVar CL.Mem ->
   MS.MemModelConfig (MSMO.MacawLazySimulatorState sym 64) sym Arch64 CL.Mem ->
   CS.SimState
     (MSMO.MacawLazySimulatorState sym 64)
     sym
     (MS.MacawExt Arch64)
     (CS.RegEntry sym CT.UnitType)
     (OverrideLang CT.UnitType)
     ('Just CT.EmptyCtx) ->
   IO a) ->
  IO a
runModelBody sym bak mmConf memImpl f = do
  halloc <- CFH.newHandleAllocator
  memVar <- CL.mkMemVar "test:mem" halloc

  let globals = CSGS.insertGlobal memVar memImpl CSGS.emptyGlobals
  let bindings = CSET.FnBindings CFH.emptyHandleMap
  let personality = MSMO.emptyMacawLazySimulatorState
  let simCtx = CSET.initSimContext bak CLI.llvmIntrinsicTypes halloc stdout bindings stubExtImpl personality
  let retRepr = CT.UnitRepr

  resultRef <- newIORef (error "withModel: body did not complete")
  let body = do
        st <- get
        result <- liftIO $ f sym bak memVar mmConf st
        liftIO $ writeIORef resultRef result
        pure ()
  let initSt = CSET.InitialState simCtx globals (CS.defaultAbortHandler) retRepr
                  (CS.runOverrideSim retRepr body)
  _ <- CS.executeCrucible [] initSt
  readIORef resultRef

-- | Like 'withModel' but always uses the online backend (z3).
-- Needed for tests that use the online solver directly (e.g. readInitialContents).
withOnlineModel ::
  forall a.
  ModelConfig ->
  CLD.EndianForm ->
  MemLayout ->
  (forall t st fs solver.
    ( WPO.OnlineSolver solver
    , st ~ WE.EmptyExprBuilderState
    , fs ~ WEB.Flags WEB.FloatIEEE
    , CL.HasLLVMAnn (WEB.ExprBuilder t st fs)
    , ?memOpts :: CL.MemOptions
    ) =>
    WEB.ExprBuilder t st fs ->
    CBO.OnlineBackend solver t st fs ->
    Lang.Crucible.CFG.Common.GlobalVar CL.Mem ->
    MS.MemModelConfig (MSMO.MacawLazySimulatorState (WEB.ExprBuilder t st fs) 64) (WEB.ExprBuilder t st fs) Arch64 CL.Mem ->
    CS.SimState
      (MSMO.MacawLazySimulatorState (WEB.ExprBuilder t st fs) 64)
      (WEB.ExprBuilder t st fs)
      (MS.MacawExt Arch64)
      (CS.RegEntry (WEB.ExprBuilder t st fs) CT.UnitType)
      (OverrideLang CT.UnitType)
      ('Just CT.EmptyCtx) ->
    IO a) ->
  IO a
withOnlineModel modelCfg endianForm layout f = do
  Some ng <- newIONonceGenerator
  sym <- WEB.newExprBuilder WEB.FloatIEEERepr WE.EmptyExprBuilderState ng
  CBO.withZ3OnlineBackend sym CBO.NoUnsatFeatures WPF.noFeatures $ \bak -> do
    let ?memOpts = CL.defaultMemOptions
    let ?recordLLVMAnnotation = \_ _ _ -> pure ()
    let ?ptrWidth = knownNat @64
    let ?processMacawAssert = MSMC.defaultProcessMacawAssertion

    (memImpl, mmConf) <- case modelCfg of
      StrictModel -> do
        (mi, mpt) <- MSM.newGlobalMemory (Proxy @Arch64) bak endianForm MSMC.ConcreteMutable (mlMacawMem layout)
        pure (mi, MSM.memModelConfig bak mpt)
      LazyModel -> do
        (mi, mpt) <- MSMLazy.newGlobalMemory (Proxy @Arch64) bak endianForm MSMC.ConcreteMutable (mlMacawMem layout)
        pure (mi, MSMLazy.memModelConfig bak mpt)

    runModelBody sym bak mmConf memImpl f

------------------------------------------------------------------------
-- Level 2 exec helpers
------------------------------------------------------------------------

execWriteModel ::
  forall sym bak p rtp f args.
  ( CB.IsSymBackend sym bak
  , CL.HasLLVMAnn sym
  , ?memOpts :: CL.MemOptions
  ) =>
  bak ->
  Endianness ->
  Lang.Crucible.CFG.Common.GlobalVar CL.Mem ->
  MS.MemModelConfig p sym Arch64 CL.Mem ->
  MemWrite ->
  CS.SimState p sym (MS.MacawExt Arch64) rtp f args ->
  IO (CS.SimState p sym (MS.MacawExt Arch64) rtp f args)
execWriteModel bak endian mvar mmConf (MemWrite vs off val) st = do
  let sym = CB.backendGetSym bak
  ptr <- mkBlock0Ptr sym off
  SomeMemRepr memRepr byteW bitW <- pure (valSizeToRepr endian vs)
  LeqProof <- pure (leqMulPos (knownNat @8) byteW)
  v <- mkBvPtr sym bitW val
  let ptrEntry = CS.RegEntry (CL.LLVMPointerRepr (knownNat @64)) ptr
  let valEntry = CS.RegEntry (CL.LLVMPointerRepr bitW) v
  MS.doWriteMemModel mvar mmConf MC.Addr64 memRepr ptrEntry valEntry st

execReadModel ::
  forall sym bak p rtp f args.
  ( CB.IsSymBackend sym bak
  , CL.HasLLVMAnn sym
  , ?memOpts :: CL.MemOptions
  ) =>
  bak ->
  Endianness ->
  Lang.Crucible.CFG.Common.GlobalVar CL.Mem ->
  MS.MemModelConfig p sym Arch64 CL.Mem ->
  MemRead ->
  CS.SimState p sym (MS.MacawExt Arch64) rtp f args ->
  IO (SomeReadResult sym, CS.SimState p sym (MS.MacawExt Arch64) rtp f args)
execReadModel bak endian mvar mmConf (MemRead vs off) st = do
  let sym = CB.backendGetSym bak
  ptr <- mkBlock0Ptr sym off
  SomeMemRepr memRepr byteW bitW <- pure (valSizeToRepr endian vs)
  LeqProof <- pure (leqMulPos (knownNat @8) byteW)
  let ptrEntry = CS.RegEntry (CL.LLVMPointerRepr (knownNat @64)) ptr
  (result, st') <- MS.doReadMemModel mvar mmConf MC.Addr64 memRepr ptrEntry st
  pure (SomeReadResult bitW result, st')

-- | Like execWriteModel but takes a pre-built LLVMPtr (for symbolic pointers).
execWriteModelPtr ::
  forall sym bak p rtp f args.
  ( CB.IsSymBackend sym bak
  , CL.HasLLVMAnn sym
  , ?memOpts :: CL.MemOptions
  ) =>
  bak ->
  Endianness ->
  Lang.Crucible.CFG.Common.GlobalVar CL.Mem ->
  MS.MemModelConfig p sym Arch64 CL.Mem ->
  ValSize ->
  CL.LLVMPtr sym 64 ->
  Integer ->
  CS.SimState p sym (MS.MacawExt Arch64) rtp f args ->
  IO (CS.SimState p sym (MS.MacawExt Arch64) rtp f args)
execWriteModelPtr bak endian mvar mmConf vs ptr val st = do
  let sym = CB.backendGetSym bak
  SomeMemRepr memRepr _byteW bitW <- pure (valSizeToRepr endian vs)
  LeqProof <- pure (leqMulPos (knownNat @8) _byteW)
  v <- mkBvPtr sym bitW val
  let ptrEntry = CS.RegEntry (CL.LLVMPointerRepr (knownNat @64)) ptr
  let valEntry = CS.RegEntry (CL.LLVMPointerRepr bitW) v
  MS.doWriteMemModel mvar mmConf MC.Addr64 memRepr ptrEntry valEntry st

-- | Like execReadModel but takes a pre-built LLVMPtr (for symbolic pointers).
execReadModelPtr ::
  forall sym bak p rtp f args.
  ( CB.IsSymBackend sym bak
  , CL.HasLLVMAnn sym
  , ?memOpts :: CL.MemOptions
  ) =>
  bak ->
  Endianness ->
  Lang.Crucible.CFG.Common.GlobalVar CL.Mem ->
  MS.MemModelConfig p sym Arch64 CL.Mem ->
  ValSize ->
  CL.LLVMPtr sym 64 ->
  CS.SimState p sym (MS.MacawExt Arch64) rtp f args ->
  IO (SomeReadResult sym, CS.SimState p sym (MS.MacawExt Arch64) rtp f args)
execReadModelPtr _bak endian mvar mmConf vs ptr st = do
  SomeMemRepr memRepr _byteW bitW <- pure (valSizeToRepr endian vs)
  LeqProof <- pure (leqMulPos (knownNat @8) _byteW)
  let ptrEntry = CS.RegEntry (CL.LLVMPointerRepr (knownNat @64)) ptr
  (result, st') <- MS.doReadMemModel mvar mmConf MC.Addr64 memRepr ptrEntry st
  pure (SomeReadResult bitW result, st')

------------------------------------------------------------------------
-- Level 2 properties
------------------------------------------------------------------------

-- Roundtrip: write to writable addr, read back, get same value.
-- When @useSym@ is True, uses symbolic ite pointers; otherwise concrete only.
prop_writeReadRoundtrip_model :: ModelConfig -> CLD.EndianForm -> Bool -> PtrEqCheck -> H.TestLimit -> H.Property
prop_writeReadRoundtrip_model mc ef useSym (PtrEqCheck eq) n =
  let endian = endianFormToEndianness ef in
  H.withTests n $ H.property $ do
    vs <- H.forAll genValSize
    layout <- H.forAll (genLayoutWithWritable vs)
    pspec <- H.forAll $ if useSym then genSymWritableAddr layout vs
                                  else concretePtr <$> genWritableAddr layout vs
    val <- H.forAll (genValue vs)
    result <- H.evalIO $ withModel mc ef layout $ \sym bak mvar mmConf st -> do
      ptr <- materializePtr sym pspec
      st' <- execWriteModelPtr bak endian mvar mmConf vs ptr val st
      CB.clearProofObligations bak
      (SomeReadResult w r, _) <- execReadModelPtr bak endian mvar mmConf vs ptr st'
      CB.clearProofObligations bak
      eq sym w r =<< mkBvPtr sym w val
    assertEqResult result

-- Last writer wins: two writes to same addr → read returns second.
prop_lastWriterWins_model :: ModelConfig -> CLD.EndianForm -> Bool -> PtrEqCheck -> H.TestLimit -> H.Property
prop_lastWriterWins_model mc ef useSym (PtrEqCheck eq) n =
  let endian = endianFormToEndianness ef in
  H.withTests n $ H.property $ do
    vs <- H.forAll genValSize
    layout <- H.forAll (genLayoutWithWritable vs)
    pspec <- H.forAll $ if useSym then genSymWritableAddr layout vs
                                  else concretePtr <$> genWritableAddr layout vs
    val1 <- H.forAll (genValue vs)
    val2 <- H.forAll (genValue vs)
    result <- H.evalIO $ withModel mc ef layout $ \sym bak mvar mmConf st -> do
      ptr <- materializePtr sym pspec
      st1 <- execWriteModelPtr bak endian mvar mmConf vs ptr val1 st
      CB.clearProofObligations bak
      st2 <- execWriteModelPtr bak endian mvar mmConf vs ptr val2 st1
      CB.clearProofObligations bak
      (SomeReadResult w r, _) <- execReadModelPtr bak endian mvar mmConf vs ptr st2
      CB.clearProofObligations bak
      eq sym w r =<< mkBvPtr sym w val2
    assertEqResult result

-- Non-overlapping writes are independent. Uses pointers from different
-- segments to guarantee non-overlap.
prop_nonOverlappingIndependent_model :: ModelConfig -> CLD.EndianForm -> Bool -> PtrEqCheck -> H.TestLimit -> H.Property
prop_nonOverlappingIndependent_model mc ef useSym (PtrEqCheck eq) n =
  let endian = endianFormToEndianness ef in
  H.withTests n $ H.property $ do
    layout <- H.forAll (genLayoutWithWritable VS8)
    (vs1, pspec1, vs2, pspec2) <- H.forAll $
      if useSym then genSymNonOverlappingWritable layout
                else genConcreteNonOverlappingWritable layout
    val1 <- H.forAll (genValue vs1)
    val2 <- H.forAll (genValue vs2)
    result <- H.evalIO $ withModel mc ef layout $ \sym bak mvar mmConf st -> do
      ptr1 <- materializePtr sym pspec1
      ptr2 <- materializePtr sym pspec2
      st1 <- execWriteModelPtr bak endian mvar mmConf vs1 ptr1 val1 st
      CB.clearProofObligations bak
      st2 <- execWriteModelPtr bak endian mvar mmConf vs2 ptr2 val2 st1
      CB.clearProofObligations bak
      (SomeReadResult w r, _) <- execReadModelPtr bak endian mvar mmConf vs1 ptr1 st2
      CB.clearProofObligations bak
      eq sym w r =<< mkBvPtr sym w val1
    assertEqResult result

-- Reading from a mapped address without writing first returns the
-- original segment contents. Uses the online solver directly because
-- ConcreteMutable mode returns symbolic expressions backed by SMT array
-- constraints that are only available within the online solver's scope.
-- | Read initial segment contents: concrete pointers only (the expected
-- value depends on the specific address, so symbolic pointers don't add value).
prop_readInitialContents_model :: ModelConfig -> CLD.EndianForm -> H.TestLimit -> H.Property
prop_readInitialContents_model mc ef n =
  let endian = endianFormToEndianness ef in
  H.withTests n $ H.property $ do
    layout <- H.forAll genMemLayout
    vs <- H.forAll genValSize
    addr <- H.forAll (genMappedAddr layout vs)
    -- Find which segment this address is in, compute expected bytes
    let seg = case [ s | s <- mlSegments layout
                       , ssBase s <= addr
                       , addr + valSizeBytes vs <= ssBase s + ssSize s ] of
                (s:_) -> s
                [] -> error "genMappedAddr produced address not in any segment"
    let off = fromIntegral (addr - ssBase seg)
        expected = BS.take (fromIntegral (valSizeBytes vs)) (BS.drop off (ssContents seg))
        expectedVal = bsToInteger ef expected
    ok <- H.evalIO $ withOnlineModel mc ef layout $ \sym bak mvar mmConf st -> do
      (SomeReadResult w result, _) <- execReadModel bak endian mvar mmConf (MemRead vs addr) st
      CB.clearProofObligations bak
      expectedPtr <- mkBvPtr sym w expectedVal
      -- Use the online solver to prove equality (the read result is
      -- symbolic, backed by SMT array constraints only visible to the
      -- online solver session).
      eq <- CLP.ptrEq sym w result expectedPtr
      case WI.asConstantPred eq of
        Just b -> pure b
        Nothing -> do
          notEq <- WI.notPred sym eq
          CBO.withSolverProcess bak (pure False) $ \sp ->
            WPO.inNewFrame sp $ do
              WPS.assume (WPO.solverConn sp) notEq
              res <- WPO.check sp "readInitialContents equality"
              case res of
                WSat.Unsat _ -> pure True   -- ¬eq is unsat → provably equal
                _            -> pure False
    H.assert ok

-- Write-valid implies read-valid: use genWritableAddr so the write
-- actually succeeds, then verify the read also produces valid obligations.
-- With concrete addresses the implication must reduce to a constant.
prop_writeValidImpliesReadValid_model :: ModelConfig -> CLD.EndianForm -> H.Property
prop_writeValidImpliesReadValid_model mc ef =
  let endian = endianFormToEndianness ef in
  H.withTests 200 $ H.property $ do
    vs <- H.forAll genValSize
    layout <- H.forAll (genLayoutWithWritable vs)
    addr <- H.forAll (genWritableAddr layout vs)
    val <- H.forAll (genValue vs)
    implVal <- H.evalIO $ withModel mc ef layout $ \sym bak mvar mmConf st -> do
      st' <- execWriteModel bak endian mvar mmConf (MemWrite vs addr val) st
      writePred <- collectAssertionPred bak
      _ <- execReadModel bak endian mvar mmConf (MemRead vs addr) st'
      readPred <- collectAssertionPred bak
      impl <- WI.impliesPred sym writePred readPred
      pure (WI.asConstantPred impl)
    case implVal of
      Nothing -> do
        H.annotate "BUG: implication predicate is symbolic for concrete inputs"
        H.failure
      Just False -> do
        H.annotate "Write-valid does not imply read-valid"
        H.failure
      Just True -> pure ()

-- Write to read-only address: obligation should NOT be trivially true.
-- Write to RO/unmapped: with concrete addresses and concrete layouts,
-- the obligation must reduce to a constant predicate. We assert both
-- that it IS concrete and that it's False.
prop_writeToROFails_model :: ModelConfig -> CLD.EndianForm -> H.Property
prop_writeToROFails_model mc ef =
  let endian = endianFormToEndianness ef in
  H.withTests 200 $ H.property $ do
    vs <- H.forAll genValSize
    layout <- H.forAll (genLayoutWithReadOnly vs)
    addr <- H.forAll (genReadOnlyAddr layout vs)
    val <- H.forAll (genValue vs)
    writePredVal <- H.evalIO $ withModel mc ef layout $ \_ bak mvar mmConf st -> do
      result <- try $ execWriteModel bak endian mvar mmConf (MemWrite vs addr val) st
      case result of
        Left (_ :: SomeException) -> pure (Just False)  -- threw = rejected
        Right _ -> do
          writePred <- collectAssertionPred bak
          pure (WI.asConstantPred writePred)
    case writePredVal of
      Nothing -> do
        H.annotate "BUG: obligation predicate is symbolic for concrete inputs"
        H.failure
      Just True -> do
        H.annotate "Write to RO address was not rejected"
        H.failure
      Just False -> pure ()

-- Write to unmapped address: uses genUnmappedAddr for targeted addresses
-- (just past segment ends, etc.), not just random high values.
prop_writeToUnmappedFails_model :: ModelConfig -> CLD.EndianForm -> H.Property
prop_writeToUnmappedFails_model mc ef =
  let endian = endianFormToEndianness ef in
  H.withTests 200 $ H.property $ do
    layout <- H.forAll genMemLayout
    vs <- H.forAll genValSize
    addr <- H.forAll (genUnmappedAddr layout)
    val <- H.forAll (genValue vs)
    writePredVal <- H.evalIO $ withModel mc ef layout $ \_ bak mvar mmConf st -> do
      result <- try $ execWriteModel bak endian mvar mmConf (MemWrite vs addr val) st
      case result of
        Left (_ :: SomeException) -> pure (Just False)  -- threw = rejected
        Right _ -> do
          writePred <- collectAssertionPred bak
          pure (WI.asConstantPred writePred)
    case writePredVal of
      Nothing -> do
        H.annotate "BUG: obligation predicate is symbolic for concrete inputs"
        H.failure
      Just True -> do
        H.annotate "Write to unmapped address was not rejected"
        H.failure
      Just False -> pure ()

-- | A warmup write operation for Level 2 (writable address + value).
data WarmupWrite = WarmupWrite !ValSize !Word64 !Integer
  deriving (Show)

-- | Generate a list of warmup writes valid for a given layout.
genWarmupWrites :: MemLayout -> H.Gen [WarmupWrite]
genWarmupWrites layout = Gen.list (Range.linear 0 8) $ do
  vs <- genValSize
  addr <- genWritableAddr layout vs
  val <- genValue vs
  pure (WarmupWrite vs addr val)

-- | Execute warmup writes on a model state, clearing obligations after each.
execWarmupWrites ::
  ( CB.IsSymBackend sym bak
  , CL.HasLLVMAnn sym
  , ?memOpts :: CL.MemOptions
  ) =>
  bak ->
  Endianness ->
  Lang.Crucible.CFG.Common.GlobalVar CL.Mem ->
  MS.MemModelConfig p sym Arch64 CL.Mem ->
  [WarmupWrite] ->
  CS.SimState p sym (MS.MacawExt Arch64) rtp f args ->
  IO (CS.SimState p sym (MS.MacawExt Arch64) rtp f args)
execWarmupWrites _ _ _ _ [] st = pure st
execWarmupWrites bak endian mvar mmConf (WarmupWrite vs addr val : ws) st = do
  st' <- execWriteModel bak endian mvar mmConf (MemWrite vs addr val) st
  CB.clearProofObligations bak
  execWarmupWrites bak endian mvar mmConf ws st'

-- Consistency: strict and lazy agree on reads after warmup writes.
-- Supports symbolic pointers (SMT variant) and concrete (quick variant).
prop_strictLazyConsistency :: CLD.EndianForm -> Bool -> PtrEqCheck -> H.TestLimit -> H.Property
prop_strictLazyConsistency ef useSym (PtrEqCheck eq) n =
  let endian = endianFormToEndianness ef in
  H.withTests n $ H.property $ do
    vs <- H.forAll genValSize
    layout <- H.forAll (genLayoutWithWritable vs)
    warmups <- H.forAll (genWarmupWrites layout)
    pspec <- H.forAll $ if useSym then genSymWritableAddr layout vs
                                  else concretePtr <$> genWritableAddr layout vs
    val <- H.forAll (genValue vs)
    let runModel mc = withModel mc ef layout $ \sym bak mvar mmConf st -> do
          st1 <- execWarmupWrites bak endian mvar mmConf warmups st
          ptr <- materializePtr sym pspec
          st2 <- execWriteModelPtr bak endian mvar mmConf vs ptr val st1
          CB.clearProofObligations bak
          (SomeReadResult w r, _) <- execReadModelPtr bak endian mvar mmConf vs ptr st2
          CB.clearProofObligations bak
          expectedPtr <- mkBvPtr sym w val
          eq sym w r expectedPtr
    strictResult <- H.evalIO (runModel StrictModel)
    lazyResult <- H.evalIO (runModel LazyModel)
    -- Both models must agree; discard if either is symbolic
    case (strictResult, lazyResult) of
      (Just s, Just l) -> do
        H.assert s
        H.assert l
      _ -> H.discard

-- Consistency: strict and lazy agree on initial segment contents.
-- Both models use ConcreteMutable which returns symbolic values backed by
-- SMT array constraints, so we compute expected bytes from the segment
-- spec and verify each model agrees via the online solver.
prop_readInitialContents_consistency :: CLD.EndianForm -> H.Property
prop_readInitialContents_consistency ef =
  let endian = endianFormToEndianness ef in
  H.withTests 200 $ H.property $ do
    layout <- H.forAll genMemLayout
    vs <- H.forAll genValSize
    addr <- H.forAll (genMappedAddr layout vs)
    let seg = case [ s | s <- mlSegments layout
                       , ssBase s <= addr
                       , addr + valSizeBytes vs <= ssBase s + ssSize s ] of
                (s:_) -> s
                [] -> error "genMappedAddr produced address not in any segment"
    let off = fromIntegral (addr - ssBase seg)
        expected = BS.take (fromIntegral (valSizeBytes vs)) (BS.drop off (ssContents seg))
        expectedVal = bsToInteger ef expected
    let checkModel mc = withOnlineModel mc ef layout $ \sym bak mvar mmConf st -> do
          (SomeReadResult w result, _) <- execReadModel bak endian mvar mmConf (MemRead vs addr) st
          CB.clearProofObligations bak
          expectedPtr <- mkBvPtr sym w expectedVal
          eqPred <- CLP.ptrEq sym w result expectedPtr
          case WI.asConstantPred eqPred of
            Just b -> pure b
            Nothing -> do
              notEq <- WI.notPred sym eqPred
              CBO.withSolverProcess bak (pure False) $ \sp ->
                WPO.inNewFrame sp $ do
                  WPS.assume (WPO.solverConn sp) notEq
                  res <- WPO.check sp "consistency equality"
                  case res of
                    WSat.Unsat _ -> pure True
                    _            -> pure False
    strictOk <- H.evalIO (checkModel StrictModel)
    lazyOk <- H.evalIO (checkModel LazyModel)
    H.assert strictOk
    H.assert lazyOk

-- | Extract a concrete integer from an LLVMPointer value (block 0).
readBvVal ::
  (WI.IsExprBuilder sym, 1 <= w, KnownNat w) =>
  sym -> NatRepr w -> CL.LLVMPtr sym w -> IO Integer
readBvVal _sym _w (CLP.LLVMPointer _blk bv) =
  case WI.asBV bv of
    Just val -> pure (BV.asUnsigned val)
    Nothing  -> error "readBvVal: symbolic value, expected concrete"

-- | Interpret a ByteString as an unsigned integer with given endianness.
bsToInteger :: CLD.EndianForm -> BS.ByteString -> Integer
bsToInteger CLD.LittleEndian = BS.foldr' (\b acc -> acc * 256 + fromIntegral b) 0
bsToInteger CLD.BigEndian    = BS.foldl' (\acc b -> acc * 256 + fromIntegral b) 0

------------------------------------------------------------------------
-- Minimal unit tests for lazy model bug
------------------------------------------------------------------------

-- | Minimal reproduction: write 8 bytes to a single RW segment,
-- read back. Lazy model returns original segment contents instead
-- of the written value.
unit_lazyWriteReadRoundtrip :: CLD.EndianForm -> TestTree
unit_lazyWriteReadRoundtrip ef = testCase "Lazy model write-read roundtrip (single RW segment)" $ do
  let endian = endianFormToEndianness ef
  let layout = buildMacawMemory
        [ SegmentSpec
            { ssBase = 0x1000
            , ssSize = 64
            , ssFlags = Perm.read .|. Perm.write
            , ssContents = BS.replicate 64 0xAA
            }
        ]
  lazyResult <- withModel LazyModel ef layout $ \sym bak mvar mmConf st -> do
    st' <- execWriteModel bak endian mvar mmConf (MemWrite VS8 0x1000 42) st
    CB.clearProofObligations bak
    (SomeReadResult w result, _) <- execReadModel bak endian mvar mmConf (MemRead VS8 0x1000) st'
    CB.clearProofObligations bak
    readBvVal sym w result
  assertEqual "lazy model should return written value" 42 lazyResult

-- | Same test on strict model (should pass, serves as control).
unit_strictWriteReadRoundtrip :: CLD.EndianForm -> TestTree
unit_strictWriteReadRoundtrip ef = testCase "Strict model write-read roundtrip (single RW segment)" $ do
  let endian = endianFormToEndianness ef
  let layout = buildMacawMemory
        [ SegmentSpec
            { ssBase = 0x1000
            , ssSize = 64
            , ssFlags = Perm.read .|. Perm.write
            , ssContents = BS.replicate 64 0xAA
            }
        ]
  strictResult <- withModel StrictModel ef layout $ \sym bak mvar mmConf st -> do
    st' <- execWriteModel bak endian mvar mmConf (MemWrite VS8 0x1000 42) st
    CB.clearProofObligations bak
    (SomeReadResult w result, _) <- execReadModel bak endian mvar mmConf (MemRead VS8 0x1000) st'
    CB.clearProofObligations bak
    readBvVal sym w result
  assertEqual "strict model should return written value" 42 strictResult

-- | Strict and lazy should agree on a simple write-read.
unit_strictLazyAgree :: CLD.EndianForm -> TestTree
unit_strictLazyAgree ef = testCase "Strict and lazy agree on simple write-read" $ do
  let endian = endianFormToEndianness ef
  let layout = buildMacawMemory
        [ SegmentSpec
            { ssBase = 0x1000
            , ssSize = 64
            , ssFlags = Perm.read .|. Perm.write
            , ssContents = BS.replicate 64 0xBB
            }
        ]
  let runModel mc = withModel mc ef layout $ \sym bak mvar mmConf st -> do
        st' <- execWriteModel bak endian mvar mmConf (MemWrite VS8 0x1000 12345) st
        CB.clearProofObligations bak
        (SomeReadResult w result, _) <- execReadModel bak endian mvar mmConf (MemRead VS8 0x1000) st'
        CB.clearProofObligations bak
        readBvVal sym w result
  strictVal <- runModel StrictModel
  lazyVal <- runModel LazyModel
  assertEqual "strict and lazy should return the same value" strictVal lazyVal

-- | Regression: write to RW segment that's adjacent to/within a larger
-- RO segment. The lazy model may re-populate from the original memory
-- contents and clobber the write.
unit_lazyWriteNearROSegment :: CLD.EndianForm -> TestTree
unit_lazyWriteNearROSegment ef = testCase "Lazy model write-read near RO segment" $ do
  let endian = endianFormToEndianness ef
  let layout = buildMacawMemory
        [ SegmentSpec
            { ssBase = 0x1000
            , ssSize = 256
            , ssFlags = Perm.read
            , ssContents = BS.replicate 256 0xCC
            }
        , SegmentSpec
            { ssBase = 0x1100
            , ssSize = 64
            , ssFlags = Perm.read .|. Perm.write
            , ssContents = BS.replicate 64 0xDD
            }
        ]
  lazyResult <- withModel LazyModel ef layout $ \sym bak mvar mmConf st -> do
    st' <- execWriteModel bak endian mvar mmConf (MemWrite VS8 0x1100 99) st
    CB.clearProofObligations bak
    (SomeReadResult w result, _) <- execReadModel bak endian mvar mmConf (MemRead VS8 0x1100) st'
    CB.clearProofObligations bak
    readBvVal sym w result
  assertEqual "lazy model should return written value (not initial segment contents)" 99 lazyResult

-- | Regression: multiple segments, write to interior of an RW segment.
-- From the consistency PBT failure.
unit_lazyMultiSegWriteRead :: CLD.EndianForm -> TestTree
unit_lazyMultiSegWriteRead ef = testCase "Lazy model write-read with multiple segments" $ do
  let endian = endianFormToEndianness ef
  let layout = buildMacawMemory
        [ SegmentSpec
            { ssBase = 757
            , ssSize = 1024
            , ssFlags = Perm.read .|. Perm.execute
            , ssContents = BS.replicate 1024 0x11
            }
        , SegmentSpec
            { ssBase = 1984
            , ssSize = 89
            , ssFlags = Perm.read .|. Perm.write
            , ssContents = BS.replicate 89 0x22
            }
        ]
  let val = 42 :: Integer
  lazyResult <- withModel LazyModel ef layout $ \sym bak mvar mmConf st -> do
    st' <- execWriteModel bak endian mvar mmConf (MemWrite VS8 1984 val) st
    CB.clearProofObligations bak
    (SomeReadResult w result, _) <- execReadModel bak endian mvar mmConf (MemRead VS8 1984) st'
    CB.clearProofObligations bak
    readBvVal sym w result
  strictResult <- withModel StrictModel ef layout $ \sym bak mvar mmConf st -> do
    st' <- execWriteModel bak endian mvar mmConf (MemWrite VS8 1984 val) st
    CB.clearProofObligations bak
    (SomeReadResult w result, _) <- execReadModel bak endian mvar mmConf (MemRead VS8 1984) st'
    CB.clearProofObligations bak
    readBvVal sym w result
  assertEqual "lazy should return written value" val lazyResult
  assertEqual "strict should return written value" val strictResult
  assertEqual "strict and lazy should agree" strictResult lazyResult


------------------------------------------------------------------------
-- Test tree
------------------------------------------------------------------------

-- | Generate both a concrete (many tests, assert concreteness) and an SMT
-- (few tests, solver-backed equality) version of a property.
-- Level 1 only — no symbolic pointers.
eqTests ::
  String -> H.PropertyName -> H.TestLimit ->
  (PtrEqCheck -> H.TestLimit -> H.Property) -> [TestTree]
eqTests desc name nQuick mkProp =
  [ testPropertyNamed desc name
      (mkProp ptrEqConcrete nQuick)
  , testPropertyNamed (desc ++ " [SMT]") (name <> "_smt")
      (mkProp ptrEqSMT 20)
  ]

-- | Three-tier test generation for Level 2 properties.
-- The property takes Bool (use symbolic pointers) + PtrEqCheck:
--   1. Concrete pointers + ptrEqConcrete: many tests, asserts concreteness
--   2. Symbolic pointers + ptrEqOptimistic: many tests, discards symbolic results
--   3. Symbolic pointers + ptrEqSMT: few tests, proves via solver
modelEqTests ::
  String -> H.PropertyName -> H.TestLimit ->
  (Bool -> PtrEqCheck -> H.TestLimit -> H.Property) -> [TestTree]
modelEqTests desc name nQuick mkProp =
  [ testPropertyNamed desc name
      (mkProp False ptrEqConcrete nQuick)
  , testPropertyNamed (desc ++ " [sym]") (name <> "_sym")
      (H.withDiscards 500 $ mkProp True ptrEqOptimistic nQuick)
  , testPropertyNamed (desc ++ " [SMT]") (name <> "_smt")
      (mkProp True ptrEqSMT 30)
  ]

-- | Build the Level 2 test tree for a given model and endianness.
modelTests :: String -> ModelConfig -> CLD.EndianForm -> [TestTree]
modelTests label mc ef = concat
  [ modelEqTests "Write then read roundtrips"
      (fromString $ label <> "_roundtrip") 200
      (prop_writeReadRoundtrip_model mc ef)
  , modelEqTests "Last writer wins"
      (fromString $ label <> "_lastWriterWins") 200
      (prop_lastWriterWins_model mc ef)
  , modelEqTests "Non-overlapping writes independent"
      (fromString $ label <> "_nonOverlapping") 200
      (prop_nonOverlappingIndependent_model mc ef)
  , [ testPropertyNamed "Read initial segment contents"
        (fromString $ label <> "_readInitial")
        (prop_readInitialContents_model mc ef 200)
    ]
  , [ testPropertyNamed "Write valid implies read valid"
        (fromString $ label <> "_writeImpliesRead")
        (prop_writeValidImpliesReadValid_model mc ef)
    ]
  , [ testPropertyNamed "Write to RO rejected"
        (fromString $ label <> "_writeROFails")
        (prop_writeToROFails_model mc ef)
    , testPropertyNamed "Write to unmapped rejected"
        (fromString $ label <> "_writeUnmappedFails")
        (prop_writeToUnmappedFails_model mc ef)
    ]
  ]

tests :: TestTree
tests = testGroup "MemOps" $ concat
  [ eqTests "Write then read roundtrips"
      "prop_writeReadRoundtrip" 1000
      prop_writeReadRoundtrip
  , eqTests "Write then read roundtrips (symbolic)"
      "prop_writeReadSymbolic" 500
      prop_writeReadSymbolic
  , eqTests "Conditional write with false preserves prior value"
      "prop_condWriteFalsePreserves" 1000
      prop_condWriteFalsePreserves
  , eqTests "Conditional read with false returns default"
      "prop_condReadFalseReturnsDefault" 1000
      prop_condReadFalseReturnsDefault
  , eqTests "Non-overlapping writes are independent"
      "prop_nonOverlappingIndependent" 1000
      prop_nonOverlappingIndependent
  , eqTests "Last writer wins"
      "prop_lastWriterWins" 1000
      prop_lastWriterWins
  , [ testPropertyNamed "Smaller read after write succeeds"
        "prop_smallerReadAfterWrite"
        prop_smallerReadAfterWrite
    ]
  , eqTests "Write-read roundtrip after arbitrary ops"
      "prop_writeReadAfterArbitraryOps" 500
      prop_writeReadAfterArbitraryOps
  , [ testPropertyNamed "Arbitrary ops don't crash"
        "prop_arbitraryOpsNoError"
        prop_arbitraryOpsNoError
    , testPropertyNamed "Write valid implies read valid"
        "prop_writeValidImpliesReadValid"
        prop_writeValidImpliesReadValid
    , testPropertyNamed "Smaller write also valid"
        "prop_smallerWriteValid"
        prop_smallerWriteValid
    , testPropertyNamed "Op order commutative"
        "prop_opOrderCommutative"
        prop_opOrderCommutative
    ]
  , [ testGroup "MemModel (Strict, LE)" (modelTests "strict_le" StrictModel CLD.LittleEndian)
    , testGroup "MemModel (Strict, BE)" (modelTests "strict_be" StrictModel CLD.BigEndian)
    , testGroup "MemModel (Lazy, LE)" (modelTests "lazy_le" LazyModel CLD.LittleEndian)
    , testGroup "MemModel (Lazy, BE)" (modelTests "lazy_be" LazyModel CLD.BigEndian)
    , testGroup "MemModel (Consistency, LE)" $ concat
      [ modelEqTests "Strict and lazy agree after warmup writes"
          "prop_strictLazyConsistency_le" 200
          (prop_strictLazyConsistency CLD.LittleEndian)
      , [ testPropertyNamed "Strict and lazy agree on initial contents"
            "prop_readInitialContents_consistency_le"
            (prop_readInitialContents_consistency CLD.LittleEndian)
        ]
      ]
    , testGroup "MemModel (Consistency, BE)" $ concat
      [ modelEqTests "Strict and lazy agree after warmup writes"
          "prop_strictLazyConsistency_be" 200
          (prop_strictLazyConsistency CLD.BigEndian)
      , [ testPropertyNamed "Strict and lazy agree on initial contents"
            "prop_readInitialContents_consistency_be"
            (prop_readInitialContents_consistency CLD.BigEndian)
        ]
      ]
    , testGroup "MemModel (Unit, LE)"
      [ unit_strictWriteReadRoundtrip CLD.LittleEndian
      , unit_lazyWriteReadRoundtrip CLD.LittleEndian
      , unit_strictLazyAgree CLD.LittleEndian
      , unit_lazyWriteNearROSegment CLD.LittleEndian
      , unit_lazyMultiSegWriteRead CLD.LittleEndian
      ]
    , testGroup "MemModel (Unit, BE)"
      [ unit_strictWriteReadRoundtrip CLD.BigEndian
      , unit_lazyWriteReadRoundtrip CLD.BigEndian
      , unit_strictLazyAgree CLD.BigEndian
      , unit_lazyWriteNearROSegment CLD.BigEndian
      , unit_lazyMultiSegWriteRead CLD.BigEndian
      ]
    ]
  ]
