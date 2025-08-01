{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Functionality that is shared between multiple memory models.
module Data.Macaw.Symbolic.Memory.Common
  ( MemoryModelContents(..)
  , toCrucibleEndian
  , fromCrucibleEndian
  , GlobalMemoryHooks(..)
  , defaultGlobalMemoryHooks

  , mkGlobalPointerValidityPredCommon
  , MacawProcessAssertion
  , MacawError(..)
  , defaultProcessMacawAssertion
  , mapRegionPointersCommon
  , populateMemChunkBytes
  , memArrEqualityAssumption
  , pleatM
  , ipleatM
  ) where

import           GHC.TypeLits

import qualified Control.Lens as L
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import qualified Data.Foldable.WithIndex as FWI
import qualified Data.IntervalMap.Strict as IM

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Macaw.CFG as MC
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.Simulator as CS
import           Text.Printf ( printf )
import qualified What4.Expr.App as WEA
import qualified What4.Expr.BoolMap as BoolMap
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI

import qualified Data.Macaw.Symbolic as MS

-- | A configuration knob controlling how the initial contents of the memory
-- model are populated
--
-- The fundamental question is how to treat global data.  It is (generally) safe
-- to make read only data concrete, as it cannot change during normal execution
-- (ignoring cases where the program uses mprotect or similar calls to change
-- memory permissions at runtime).
--
-- If we are trying to prove properties about functions in isolation, though, we
-- have to assume that non-constant global data can have /any/ value, which
-- means that we have to represent each byte as symbolic.  This will change when
-- we start pursuing compositional verification and want to have more elaborate
-- memory setups.
--
-- Note that using concrete mutable data from the binary image is unsafe, but
-- may be useful in some cases.
data MemoryModelContents = SymbolicMutable
                         -- ^ All mutable global data is fully symbolic, but
                         -- read-only data is concrete (and taken from the
                         -- memory image of the binary)
                         | ConcreteMutable
                         -- ^ All of the global data is taken from the binary
  deriving Eq

-- | Convert a Macaw 'MC.Endianness' to a Crucible LLVM 'CLD.EndianForm'.
toCrucibleEndian :: MC.Endianness -> CLD.EndianForm
toCrucibleEndian MC.BigEndian    = CLD.BigEndian
toCrucibleEndian MC.LittleEndian = CLD.LittleEndian

-- | Convert a Crucible LLVM 'CLD.EndianForm' to a Macaw 'MC.Endianness'.
fromCrucibleEndian :: CLD.EndianForm -> MC.Endianness
fromCrucibleEndian CLD.BigEndian    = MC.BigEndian
fromCrucibleEndian CLD.LittleEndian = MC.LittleEndian

-- | Hooks to configure the initialization of global memory
data GlobalMemoryHooks w =
  GlobalMemoryHooks {
  populateRelocation
    :: forall sym bak
       . (CB.IsSymBackend sym bak)
    => bak
    -> MC.Memory w
    -- ^ The region of memory in which the relocation is defined
    -> MC.MemSegment w
    -- ^ The segment of memory in which the relocation is defined
    -> MC.MemAddr w
    -- ^ The address of the relocation
    -> MC.Relocation w
    -> IO [WI.SymExpr sym (WI.BaseBVType 8)]
    -- ^ The symbolic bytes to represent a relocation with
    --
    -- They could be entirely unconstrained bytes, or could be distinguished
    -- bytes used to implement linking of shared libraries (i.e., relocation
    -- resolution)
  }

-- | A default set of hooks that raises errors if they encounter constructs that
-- they do not handle (because there is no sensible default behavior).
defaultGlobalMemoryHooks :: GlobalMemoryHooks w
defaultGlobalMemoryHooks =
  GlobalMemoryHooks {
    populateRelocation = \_ _ _ _ r ->
      return (error ("SymbolicRef SegmentRanges are not supported yet: " ++ show r))
    }


-- | Describes the type of error a Macaw generated predicate represents if the assertion
-- is violated. See 'MacawProcessAssertion' for information on how to consume this information 
-- via a callback.
data MacawError sym where 
  UnmappedGlobalMemoryAccess :: (1 <= w) => CS.RegValue sym (CL.LLVMPointerType w) -> MacawError sym

-- | Given a safety predicate and a description of the error it represents,
-- return a new predicate (and possibly perform additional side-effects, such as
-- recording information about the predicate). Typically the callback will want to
-- annotate the predicate via 'W4.annotateTerm' so that information about the predicate
-- can be found later.
type MacawProcessAssertion sym
  = (?processMacawAssert :: sym -> WI.Pred sym -> MacawError sym -> IO (WI.Pred sym))


-- | A default 'MacawProcessAssertion' implementation that simply returns the original predicate
-- with no effect.
defaultProcessMacawAssertion :: sym -> WI.Pred sym -> MacawError sym -> IO (WI.Pred sym)
defaultProcessMacawAssertion _ p _  = pure p


-- | The shared implementation for the @mkGlobalPointerValidityPred@ function in
-- the default memory model ("Data.Macaw.Symbolic.Memory") and the lazy memory
-- model ("Data.Macaw.Symbolic.Memory.Lazy").
mkGlobalPointerValidityPredCommon ::
     forall sym w
   . ( CB.IsSymInterface sym
     , MC.MemWidth w
     , MacawProcessAssertion sym
     )
  => IM.IntervalMap (MC.MemWord w) CL.Mutability
  -> MS.MkGlobalPointerValidityAssertion sym w
mkGlobalPointerValidityPredCommon tbl sym puse mcond ptr = do
  let w = MC.memWidthNatRepr @w

  -- If this is a write, the pointer cannot be in an immutable range (so just
  -- return False for the predicate on that range).
  --
  -- Otherwise, the pointer is allowed to be between the lo/hi range
  let inMappedRange off (range, mut)
        | MS.pointerUseTag puse == MS.PointerWrite && mut == CL.Immutable = return (WI.falsePred sym)
        | otherwise =
          case range of
            IM.IntervalCO lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUle sym lobv off
              hib <- WI.bvUlt sym off hibv
              WI.andPred sym lob hib
            IM.ClosedInterval lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUle sym lobv off
              hib <- WI.bvUle sym off hibv
              WI.andPred sym lob hib
            IM.OpenInterval lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUlt sym lobv off
              hib <- WI.bvUlt sym off hibv
              WI.andPred sym lob hib
            IM.IntervalOC lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUlt sym lobv off
              hib <- WI.bvUle sym off hibv
              WI.andPred sym lob hib

  let mkPred off = do
        ps <- mapM (inMappedRange off) (IM.toList tbl)
        ps' <- WI.orOneOf sym (L.folded . id) ps
        -- Add the condition from a conditional write
        WI.itePred sym (maybe (WI.truePred sym) CS.regValue mcond) ps' (WI.truePred sym)


  let ptrVal = CS.regValue ptr
  let (ptrBase, ptrOff) = CL.llvmPointerView ptrVal
  case WI.asNat ptrBase of
    Just 0 -> do
      p <- mkPred ptrOff
      p' <- ?processMacawAssert sym p (UnmappedGlobalMemoryAccess ptrVal)
      let msg = printf "%s outside of static memory range (known BlockID 0): %s" (show (MS.pointerUseTag puse)) (show (WI.printSymExpr ptrOff))
      let loc = MS.pointerUseLocation puse
      let assertion = CB.LabeledPred p' (CS.SimError loc (CS.GenericSimError msg))
      return (Just assertion)
    Just _ -> return Nothing
    Nothing -> do
      -- In this case, we don't know for sure if the block id is 0, but it could
      -- be (it is symbolic).  The assertion has to be conditioned on the equality.
      p <- mkPred ptrOff
      zeroNat <- WI.natLit sym 0
      isZeroBase <- WI.natEq sym zeroNat ptrBase
      p' <- WI.itePred sym isZeroBase p (WI.truePred sym)
      p'' <- ?processMacawAssert sym p' (UnmappedGlobalMemoryAccess ptrVal)
      let msg = printf "%s outside of static memory range (unknown BlockID): %s" (show (MS.pointerUseTag puse)) (show (WI.printSymExpr ptrOff))
      let loc = MS.pointerUseLocation puse
      let assertion = CB.LabeledPred p'' (CS.SimError loc (CS.GenericSimError msg))
      return (Just assertion)



-- | The shared implementation for the @mapRegionPointers@ function in the
-- default memory model ("Data.Macaw.Symbolic.Memory") and the lazy memory model
-- ("Data.Macaw.Symbolic.Memory.Lazy").
mapRegionPointersCommon ::
     ( MC.MemWidth w
     , 16 <= w
     , CB.IsSymInterface sym
     , CL.HasLLVMAnn sym
     , ?memOpts :: CL.MemOptions
     )
  => CL.LLVMPtr sym w
  -> MS.GlobalMap sym CL.Mem w
mapRegionPointersCommon ptr = MS.GlobalMap $ \bak mem regionNum offsetVal ->
  let sym = CB.backendGetSym bak in
  case WI.asNat regionNum of
    Just 0 -> do
      let ?ptrWidth = WI.bvWidth offsetVal
      CL.doPtrAddOffset bak mem ptr offsetVal
    Just _ ->
      -- This is the case where the region number is concrete and non-zero,
      -- meaning that it is already an LLVM pointer
      --
      -- NOTE: This case is not possible because we only call this from
      -- 'tryGlobPtr', which handles this case separately
      return (CL.LLVMPointer regionNum offsetVal)
    Nothing -> do
      -- In this case, the region number is symbolic, so we need to be very
      -- careful to handle the possibility that it is zero (and thus must be
      -- conditionally mapped to one or all of our statically-allocated regions.
      --
      -- NOTE: We can avoid making a huge static mux over all regions: the
      -- low-level memory model code already handles building the mux tree as it
      -- walks backwards over all allocations that are live.
      --
      -- We just need to add one top-level mux:
      --
      -- > ite (blockid == 0) (translate base) (leave alone)
      let ?ptrWidth = WI.bvWidth offsetVal
      zeroNat <- WI.natLit sym 0
      isZeroRegion <- WI.natEq sym zeroNat regionNum
      -- The pointer mapped to global memory (if the region number is zero)
      globalPtr <- CL.doPtrAddOffset bak mem ptr offsetVal
      CL.muxLLVMPtr sym isZeroRegion globalPtr (CL.LLVMPointer regionNum offsetVal)

-- | Convert each byte in a 'MC.MemChunk' to the corresponding bytes. These
-- can possibly be symbolic bytes depending on the behavior of the
-- 'GlobalMemoryHooks'.
populateMemChunkBytes ::
     ( MonadIO m
     , CB.IsSymBackend sym bak
     , MC.MemWidth w
     )
  => bak
  -> GlobalMemoryHooks w
  -> MC.Memory w
  -> MC.MemSegment w
  -> MC.MemAddr w
  -> MC.MemChunk w
  -> m [WI.SymBV sym 8]
populateMemChunkBytes bak hooks mem seg addr memChunk =
  liftIO $
  case memChunk of
    MC.RelocationRegion reloc ->
      populateRelocation hooks bak mem seg addr reloc
    MC.BSSRegion sz ->
      replicate (fromIntegral sz) <$> WI.bvLit sym w8 (BV.zero w8)
    MC.ByteRegion bytes ->
      traverse (WI.bvLit sym w8 . BV.word8) $ BS.unpack bytes
  where
    sym = CB.backendGetSym bak
    w8 = WI.knownNat @8

-- | Generate an 'AB.Assumption' that particular elements of the array backing
-- global memory are equal to the appropriate bytes. This function does not add
-- the 'AB.Assumption' to the backend, so it is the responsibility of the caller
-- to decide how to assume it.
memArrEqualityAssumption ::
     forall sym w t st fs m f
   . ( sym ~ WEB.ExprBuilder t st fs
     , MC.MemWidth w
     , MonadIO m
     , FWI.FoldableWithIndex Int f
     )
  => sym
  -> WI.SymArray sym (Ctx.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8)
  -> MC.MemWord w
  -> f (WI.SymBV sym 8)
  -> m (CB.Assumption sym)
memArrEqualityAssumption sym symArray absAddr bytes = do
    -- We used to assert the equality of each byte separately.  This ended up
    -- being very slow for large binaries, as it synchronizes the pipe to the
    -- solver after each assertion. Instead, we now encode all of the initial
    -- values as equalities and generate a large conjunction that asserts them
    -- all at once.
    --
    -- The roundabout encoding below (using the low-level 'WEB.sbMakeExpr'
    -- API) is used because the natural encoding (using 'WI.andPred') attempts
    -- to apply an optimization called absorbtion (which attempts to discard
    -- redundant conjuncts). That optimization is quadratic in cost, which
    -- makes this encoding intractably expensive for large terms.  By using
    -- 'WEB.sbMakeExpr', we avoid that optimization (which will never fire for
    -- this term anyway, as there are no redundant conjuncts).
    initVals <- ipleatM [] bytes $ \idx bmvals byte -> do
      let absByteAddr = fromIntegral idx + absAddr
      index_bv <- liftIO $ WI.bvLit sym w (BV.mkBV w (toInteger absByteAddr))
      eq_pred <- liftIO $ WI.bvEq sym byte =<< WI.arrayLookup sym symArray (Ctx.singleton index_bv)
      return (eq_pred : bmvals)
    let desc = printf "Bytes@[addr=%s,nbytes=%s]" (show absAddr) (show (F.toList bytes))
    prog_loc <- liftIO $ WI.getCurrentProgramLoc sym
    let conj = WEA.ConjPred (BoolMap.ConjMap (BoolMap.fromVars [(e, BoolMap.Positive) | e <- initVals]))
    byteEqualityAssertion <- liftIO $ WEB.sbMakeExpr sym conj
    pure $ CB.GenericAssumption prog_loc desc byteEqualityAssertion
  where
    w = MC.memWidthNatRepr @w

-- | The 'pleatM' function is 'foldM' with the arguments switched so
-- that the function is last.
pleatM :: (Monad m, F.Foldable t)
       => b
       -> t a
       -> (b -> a -> m b)
       -> m b
pleatM s l f = F.foldlM f s l

-- | The 'ipleatM' function is 'FWI.ifoldM' with the arguments switched so
-- that the function is last.
ipleatM :: (Monad m, FWI.FoldableWithIndex i t)
        => b
        -> t a
        -> (i -> b -> a -> m b)
        -> m b
ipleatM s l f = FWI.ifoldlM f s l
