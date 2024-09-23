{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Symbolic.Stack
  ( stackArray
  , mallocStack
  , ArrayStack(..)
  , createArrayStack
  , allocStackSpace
  , alignStackPointer
  , writeSpilledArgs
  ) where

import Control.Monad qualified as Monad
import Data.BitVector.Sized qualified as BVS
import Data.Parameterized.Context as Ctx
import Data.Sequence qualified as Seq
import GHC.Natural (naturalToInteger)
import Lang.Crucible.Backend qualified as C
import Lang.Crucible.LLVM.Bytes qualified as Bytes
import Lang.Crucible.LLVM.DataLayout qualified as CLD
import Lang.Crucible.LLVM.MemModel qualified as CLM
import What4.Interface qualified as WI
import What4.Symbol qualified as WSym

-- | Helper, not exported
stackAlign :: CLD.Alignment
stackAlign = CLD.noAlignment

-- | Create an SMT array representing the program stack.
stackArray ::
  (1 WI.<= w) =>
  CLM.HasPtrWidth w =>
  WI.IsSymExprBuilder sym =>
  sym ->
  IO (WI.SymArray sym (Ctx.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8))
stackArray sym =
  WI.freshConstant
    sym
    (WSym.safeSymbol "stack_array")
    (WI.BaseArrayRepr (Ctx.singleton (WI.BaseBVRepr ?ptrWidth)) WI.knownRepr)

-- | Create an allocation representing the program stack, using 'CLM.doMalloc'.
--
-- This allocation is:
--
-- * mutable, because the program must write to the stack
-- * of kind 'CLM.StackAlloc'
-- * without alignment ('CLD.noAlignment')
mallocStack ::
  C.IsSymBackend sym bak =>
  CLM.HasPtrWidth w =>
  (?memOpts :: CLM.MemOptions) =>
  CLM.HasLLVMAnn sym =>
  bak ->
  CLM.MemImpl sym ->
  -- | Size of stack allocation
  WI.SymExpr sym (WI.BaseBVType w) ->
  IO (CLM.LLVMPtr sym w, CLM.MemImpl sym)
mallocStack bak mem sz =
  CLM.doMalloc bak CLM.StackAlloc CLM.Mutable "stack_alloc" mem sz stackAlign

-- | An allocation representing the program stack, backed by an SMT array
data ArrayStack sym w
  = ArrayStack
    { -- | Pointer to the base of the stack array
      arrayStackBasePtr :: CLM.LLVMPtr sym w
      -- | Pointer to the top (end) of the stack array
    , arrayStackTopPtr :: CLM.LLVMPtr sym w
      -- | SMT array backing the stack allocation
    , arrayStackVal :: WI.SymArray sym (Ctx.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8)
    }

-- | Create an SMT-array-backed stack allocation
--
-- * Creates a stack array with 'stackArray'
-- * Allocates space for the stack with 'mallocStack'
-- * Writes the stack array to the allocation
-- * Creates a pointer to the end of the stack
createArrayStack ::
  C.IsSymBackend sym bak =>
  CLM.HasPtrWidth w =>
  (?memOpts :: CLM.MemOptions) =>
  CLM.HasLLVMAnn sym =>
  bak ->
  CLM.MemImpl sym ->
  -- | Size of stack allocation
  WI.SymExpr sym (WI.BaseBVType w) ->
  IO (ArrayStack sym w, CLM.MemImpl sym)
createArrayStack bak mem sz = do
  let sym = C.backendGetSym bak
  arr <- stackArray sym
  (base, mem1) <- mallocStack bak mem sz
  mem2 <- CLM.doArrayStore bak mem1 base stackAlign arr sz

  -- Put the stack pointer at the end of the stack allocation, i.e., an offset
  -- that is one less than the allocation's size.
  off <- WI.bvSub sym sz =<< WI.bvOne sym ?ptrWidth
  top <- CLM.doPtrAddOffset bak mem2 base off
  pure (ArrayStack base top arr, mem2)

-- | Allocate stack space by subtracting from the stack pointer
--
-- This is only suitable for use with architectures/ABIs where the stack grows
-- down.
allocStackSpace ::
  C.IsSymInterface sym =>
  CLM.HasPtrWidth w =>
  sym ->
  CLM.LLVMPtr sym w ->
  WI.SymBV sym w ->
  IO (CLM.LLVMPtr sym w)
allocStackSpace sym = CLM.ptrSub sym ?ptrWidth

-- | Align the stack pointer to a particular 'CLD.Alignment'.
--
-- This is only suitable for use with architectures/ABIs where the stack grows
-- down.
alignStackPointer ::
  C.IsSymInterface sym =>
  CLM.HasPtrWidth w =>
  sym ->
  CLD.Alignment ->
  CLM.LLVMPtr sym w ->
  IO (CLM.LLVMPtr sym w)
alignStackPointer sym align orig@(CLM.LLVMPointer blk off) = do
  let alignInt = 2 ^ naturalToInteger (CLD.alignmentToExponent align)
  if alignInt == 1
  then pure orig
  else do
    -- Because the stack grows down, we can align it by simply ANDing the stack
    -- pointer with a mask with some amount of 1s followed by some amount of 0s.
    let mask = BVS.complement ?ptrWidth (BVS.mkBV ?ptrWidth (alignInt - 1))
    maskBv <- WI.bvLit sym ?ptrWidth mask
    off' <- WI.bvAndBits sym off maskBv
    pure (CLM.LLVMPointer blk off')

-- | Write pointer-sized stack-spilled arguments to the stack.
--
-- This function:
--
-- * Aligns the stack to the minimum provided 'CLD.Alignment', call this M.
-- * Potentially adds padding to ensure that after writing the arguments to the
--   stack, the resulting stack pointer will be 2M-aligned.
-- * Writes the stack-spilled arguments, in reverse order.
--
-- It is suitable for use with architectures/ABIs where the above is
-- the desired behavior, e.g., AArch32 and SysV on x86_64. However,
-- macaw-symbolic-{aarch32,x86} provide higher-level wrappers around this
-- function, so its direct use is discouraged.
--
-- Asserts that the stack allocation is writable and large enough to contain the
-- spilled arguments.
writeSpilledArgs ::
  C.IsSymBackend sym bak =>
  (?memOpts :: CLM.MemOptions) =>
  CLM.HasPtrWidth w =>
  CLM.HasLLVMAnn sym =>
  bak ->
  CLM.MemImpl sym ->
  -- | Minimum stack alignment
  CLD.Alignment ->
  CLM.LLVMPtr sym w ->
  -- | Stack spilled arguments, in normal left-to-right order
  Seq.Seq (CLM.LLVMPtr sym w) ->
  IO (CLM.LLVMPtr sym w, CLM.MemImpl sym)
writeSpilledArgs bak mem minAlign sp spilledArgs = do
  let sym = C.backendGetSym bak

  -- M is the minimum alignment, as an integer
  let m = 2 ^ CLD.alignmentToExponent minAlign

  -- First, align to M bytes. In all probability, this is a no-op.
  spAlignedMin <- alignStackPointer sym minAlign sp

  -- At this point, exactly one of `spAlignedMin` or `spAlignedMin +/- M` is
  -- 2M-byte aligned. We need to ensure that, after writing the argument list,
  -- the stack pointer will be 2M-byte aligned.
  --
  -- If `sp` is already 2M-byte aligned and there are an even number of spilled
  -- arguments, we're good. If `sp + M` is already 2M-byte aligned and there
  -- are an odd number of arguments, we're good. In the other cases, we need to
  -- subtract M from `sp`. As a table:
  --
  -- +----------------------+------+------+
  -- |                      | even | odd  |
  -- |----------------------+------+------+
  -- | 16-byte aligned      | noop | -M   |
  -- +----------------------+-------------+
  -- | not 16-byte aligned  | -M   | noop |
  -- +----------------------+-------------+
  --
  let alignMore = CLD.exponentToAlignment (CLD.alignmentToExponent minAlign + 1)
  spAlignedMore <- alignStackPointer sym alignMore sp
  isAlignedMore <- CLM.ptrEq sym ?ptrWidth spAlignedMin spAlignedMore
  sp' <-
    if even (Seq.length spilledArgs)
    then
      -- In this case, either the stack pointer is *already* 2M-byte aligned, or
      -- it *needs to be* 2M-byte aligned (which is equivalent to subtracting M,
      -- as it is already M-byte aligned). In either case, this value suffices.
      pure spAlignedMore
    else do
      mBv <- WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth m)
      spSubMore <- allocStackSpace sym spAlignedMore mBv
      CLM.muxLLVMPtr sym isAlignedMore spSubMore spAlignedMin

  let ptrBytes = WI.natValue ?ptrWidth `div` 8
  ptrBytesBv <- WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth (fromIntegral ptrBytes))
  let ptrSz = CLM.bitvectorType (Bytes.toBytes ptrBytes)
  let writeWord (p, mi) arg = do
        p' <- CLM.ptrSub sym ?ptrWidth p ptrBytesBv
        mi' <- CLM.storeRaw bak mi p' ptrSz CLD.noAlignment (CLM.ptrToPtrVal arg)
        pure (p', mi')
  Monad.foldM writeWord (sp', mem) (Seq.reverse spilledArgs)
