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
  , ExtraStackSlots(..)
  , ArrayStack(..)
  , createArrayStack
  ) where

import Data.BitVector.Sized qualified as BVS
import Data.Macaw.CFG qualified as MC
import Data.Macaw.Symbolic qualified as MS
import Data.Parameterized.Context as Ctx
import Lang.Crucible.Backend qualified as C
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.LLVM.DataLayout qualified as CLD
import Lang.Crucible.LLVM.MemModel qualified as CLM
import What4.Interface qualified as WI
import What4.Symbol qualified as WSym

-- | Helper, not exported
stackAlign :: CLD.Alignment
stackAlign = CLD.noAlignment

-- | Create an SMT array representing the program stack.
--
-- Builds a 'WI.freshConstant' with name "stack_array".
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

-- | Allocate this many pointer-sized stack slots, which are reserved for
-- stack-spilled arguments.
newtype ExtraStackSlots = ExtraStackSlots { getExtraStackSlots :: Int }
  -- Derive the Read instance using the `newtype` strategy, not the
  -- `stock` strategy. This allows parsing ExtraStackSlots values in
  -- optparse-applicative-based command-line parsers using the `Read` instance.
  deriving newtype (Enum, Eq, Integral, Num, Ord, Read, Real, Show)

-- | An allocartion representing the program stack, backed by an SMT array
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
-- * Creates a pointer to the top of the stack, which is the end minus the extra
--   stack slots
createArrayStack ::
  C.IsSymBackend sym bak =>
  CLM.HasPtrWidth w =>
  (?memOpts :: CLM.MemOptions) =>
  CLM.HasLLVMAnn sym =>
  bak ->
  CLM.MemImpl sym ->
  -- | The caller must ensure the size of these is less than the allocation size
  ExtraStackSlots ->
  -- | Size of stack allocation
  WI.SymExpr sym (WI.BaseBVType w) ->
  IO (ArrayStack sym w, CLM.MemImpl sym)
createArrayStack bak mem slots sz = do
  let sym = C.backendGetSym bak
  arr <- stackArray sym
  (base, mem1) <- mallocStack bak mem sz
  mem2 <- CLM.doArrayStore bak mem1 base stackAlign arr sz

  end <- CLM.doPtrAddOffset bak mem2 base sz
  let ptrBytes = WI.intValue ?ptrWidth `div` 8
  let slots' = fromIntegral (getExtraStackSlots slots)
  let slotsBytes = slots' * ptrBytes
  slotsBytesBv <- WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth slotsBytes)
  top <- CLM.ptrSub sym ?ptrWidth end slotsBytesBv

  pure (ArrayStack base top arr, mem2)

-- | Set the stack pointer register.
_setStackPointerReg ::
  1 WI.<= MC.ArchAddrWidth arch =>
  MS.SymArchConstraints arch =>
  C.IsSymInterface sym =>
  MS.ArchVals arch ->
  C.RegEntry sym (MS.ArchRegStruct arch) ->
  CLM.LLVMPtr sym (MC.ArchAddrWidth arch) ->
  C.RegEntry sym (MS.ArchRegStruct arch)
_setStackPointerReg archVals regs = MS.updateReg archVals regs MC.sp_reg
