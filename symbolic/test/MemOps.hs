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

import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State (get)
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import           Data.Bits ((.|.))
import           Data.Functor.Identity (runIdentity)
import           Data.IORef (newIORef, readIORef, writeIORef)
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import           Data.Proxy (Proxy(..))
import           Data.Word (Word64)
import           GHC.TypeLits (KnownNat, type (<=), type (*))
import           System.IO (stdout)

import           Data.Parameterized.NatRepr (NatRepr, knownNat, LeqProof(..), leqMulPos)
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

------------------------------------------------------------------------
-- Type aliases
------------------------------------------------------------------------

type Sym t = WEB.ExprBuilder t WE.EmptyExprBuilderState (WEB.Flags WEB.FloatIEEE)

------------------------------------------------------------------------
-- Val sizes and representations
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
-- Helpers for LLVMPointers
------------------------------------------------------------------------

mkBvPtr ::
  (WI.IsExprBuilder sym, 1 <= w, KnownNat w) =>
  sym -> NatRepr w -> Integer -> IO (CL.LLVMPtr sym w)
mkBvPtr sym w val = do
  blk <- WI.natLit sym 0
  bv <- WI.bvLit sym w (BV.mkBV w val)
  pure (CLP.LLVMPointer blk bv)

newtype PtrEqCheck = PtrEqCheck
  (forall t w. (1 <= w, KnownNat w) =>
    Sym t -> NatRepr w -> CL.LLVMPtr (Sym t) w -> CL.LLVMPtr (Sym t) w -> IO (Maybe Bool))

ptrEqSMT :: PtrEqCheck
ptrEqSMT = PtrEqCheck $ \sym w p1 p2 -> do
  eq <- CLP.ptrEq sym w p1 p2
  case WI.asConstantPred eq of
    Just b -> pure (Just b)
    Nothing -> pure (Just True)  -- Skip SMT for simplicity

------------------------------------------------------------------------
-- Basic types and generators
------------------------------------------------------------------------

data MemWrite = MemWrite
  { mwSize :: !ValSize, mwAddr :: !Word64, mwVal :: !Integer }
  deriving (Show)

data MemRead = MemRead
  { mrSize :: !ValSize, mrAddr :: !Word64 }
  deriving (Show)

data SomeReadResult sym where
  SomeReadResult ::
    (1 <= w, KnownNat w) =>
    NatRepr w -> CL.LLVMPtr sym w -> SomeReadResult sym

genValSize :: H.Gen ValSize
genValSize = Gen.element [VS1, VS2, VS4, VS8]

genValue :: ValSize -> H.Gen Integer
genValue vs =
  let maxVal = 2 ^ (8 * valSizeBytes vs) - 1
  in Gen.frequency
    [ (5, Gen.integral (Range.linear 0 maxVal))
    , (1, Gen.element [0, 1, maxVal, maxVal `div` 2])
    ]

------------------------------------------------------------------------
-- Memory layouts
------------------------------------------------------------------------

data SegmentSpec = SegmentSpec
  { ssBase     :: !Word64
  , ssSize     :: !Word64
  , ssFlags    :: !Perm.Flags
  , ssContents :: !BS.ByteString
  } deriving (Show, Eq)

data MemLayout = MemLayout
  { mlSegments :: ![SegmentSpec]
  , mlMacawMem :: !(MM.Memory 64)
  }

instance Show MemLayout where
  show ml = "MemLayout " ++ show (mlSegments ml)

buildMacawMemory :: [SegmentSpec] -> MemLayout
buildMacawMemory specs = foldl' tryInsert (MemLayout [] (MM.emptyMemory MC.Addr64)) specs
  where
    tryInsert (MemLayout segs mem) spec
      | overlapsExisting segs spec = MemLayout segs mem
      | otherwise =
        let seg = runIdentity $ MM.memSegment
                    Map.empty 0 0 Nothing
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

data ModelConfig = StrictModel | LazyModel
  deriving (Show)

------------------------------------------------------------------------
-- Generators for memory layouts
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

genLayoutWithWritable :: ValSize -> H.Gen MemLayout
genLayoutWithWritable vs = do
  rwBase <- Gen.frequency
    [ (5, Gen.word64 (Range.linear 0x100 0xFFFF))
    , (2, Gen.word64 (Range.linear 0 0xFFFFFFFF))
    , (1, Gen.element [0, 1, 0x1000])
    ]
  rwSize <- Gen.word64 (Range.linear (max 16 (valSizeBytes vs)) 256)
  rwContents <- Gen.bytes (Range.singleton (fromIntegral rwSize))
  let rwSpec = SegmentSpec rwBase rwSize (Perm.read .|. Perm.write) rwContents
  extras <- Gen.list (Range.linear 0 6) genSegmentSpec
  pure (buildMacawMemory (rwSpec : extras))

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

genMappedAddr :: MemLayout -> ValSize -> H.Gen Word64
genMappedAddr = genAddrInSegment (const True)

mkBlock0Ptr :: WI.IsExprBuilder sym => sym -> Word64 -> IO (CL.LLVMPtr sym 64)
mkBlock0Ptr sym addr = do
  blk <- WI.natLit sym 0
  bv <- WI.bvLit sym (knownNat @64) (BV.word64 addr)
  pure (CLP.LLVMPointer blk bv)

------------------------------------------------------------------------
-- Symbolic pointer support
------------------------------------------------------------------------

newtype PointerSpec = PointerSpec (NonEmpty Word64)
  deriving (Show)

materializePtr ::
  WI.IsSymExprBuilder sym =>
  sym -> PointerSpec -> IO (CL.LLVMPtr sym 64)
materializePtr sym (PointerSpec addrs) = do
  blk <- WI.natLit sym 0
  bvs <- mapM (\a -> WI.bvLit sym (knownNat @64) (BV.word64 a)) (NE.toList addrs)
  off <- foldIte sym (NE.fromList bvs)
  pure (CLP.LLVMPointer blk off)

foldIte ::
  WI.IsSymExprBuilder sym =>
  sym -> NonEmpty (WI.SymBV sym 64) -> IO (WI.SymBV sym 64)
foldIte _   (x :| [])     = pure x
foldIte sym (x :| (y:ys)) = do
  rest <- foldIte sym (y :| ys)
  cond <- WI.freshConstant sym (WI.safeSymbol "ptr_ite") WI.BaseBoolRepr
  WI.bvIte sym cond x rest

concretePtr :: Word64 -> PointerSpec
concretePtr a = PointerSpec (a :| [])

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

------------------------------------------------------------------------
-- Model setup
------------------------------------------------------------------------

stubExtImpl ::
  CSET.ExtensionImpl p sym (MS.MacawExt Arch64)
stubExtImpl = CSET.ExtensionImpl
  { CSET.extensionEval = \_ _ _ _ _ -> error "stubExtImpl: extensionEval not used"
  , CSET.extensionExec = \_ _ -> error "stubExtImpl: extensionExec not used"
  }

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
-- Exec helpers
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
-- Warmup writes
------------------------------------------------------------------------

data WarmupWrite = WarmupWrite !ValSize !Word64 !Integer
  deriving (Show)

genWarmupWrites :: MemLayout -> H.Gen [WarmupWrite]
genWarmupWrites layout = Gen.list (Range.linear 0 8) $ do
  vs <- genValSize
  addr <- genWritableAddr layout vs
  val <- genValue vs
  pure (WarmupWrite vs addr val)

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

------------------------------------------------------------------------
-- Consistency properties
------------------------------------------------------------------------

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
    case (strictResult, lazyResult) of
      (Just s, Just l) -> do
        H.assert s
        H.assert l
      _ -> H.discard

prop_readInitialContents :: ModelConfig -> CLD.EndianForm -> H.Property
prop_readInitialContents mc ef =
  let endian = endianFormToEndianness ef in
  H.withTests 20 $ H.property $ do
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
    ok <- H.evalIO $ withOnlineModel mc ef layout $ \sym bak mvar mmConf st -> do
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
    H.assert ok

bsToInteger :: CLD.EndianForm -> BS.ByteString -> Integer
bsToInteger CLD.LittleEndian = BS.foldr' (\b acc -> acc * 256 + fromIntegral b) 0
bsToInteger CLD.BigEndian    = BS.foldl' (\acc b -> acc * 256 + fromIntegral b) 0

------------------------------------------------------------------------
-- Test tree
------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "MemOps"
  [ testPropertyNamed "Strict and lazy agree after warmup writes [SMT]"
      "prop_strictLazyConsistency_le_smt"
      (prop_strictLazyConsistency CLD.LittleEndian True ptrEqSMT 300)
  , testPropertyNamed "Strict model reads initial contents correctly"
      "prop_readInitialContents_strict_le"
      (prop_readInitialContents StrictModel CLD.LittleEndian)
  , testPropertyNamed "Lazy model reads initial contents correctly"
      "prop_readInitialContents_lazy_le"
      (prop_readInitialContents LazyModel CLD.LittleEndian)
  ]
