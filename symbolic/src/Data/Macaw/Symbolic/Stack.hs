{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Symbolic.Stack
  ( stackArray
  , mallocStack
  , ArrayStack(..)
  , createArrayStack
  ) where

import Data.Parameterized.Context as Ctx

import qualified What4.Interface as WI
import qualified What4.Symbol as WSym

import qualified Lang.Crucible.Backend as C

import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as CLM

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

data ArrayStack sym w
  = ArrayStack
    { -- | Pointer to the base of the stack array
      arrayStackPtr :: CLM.LLVMPtr sym w
      -- | SMT array backing the stack allocation
    , arrayStackVal :: WI.SymArray sym (Ctx.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8)
    }

-- | Create an SMT-array-backed stack allocation
--
-- * Creates a stack array with 'stackArray'
-- * Allocates space for the stack with 'mallocStack'
-- * Writes the stack array to the allocation
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
  (ptr, mem1) <- mallocStack bak mem sz
  mem2 <- CLM.doArrayStore bak mem1 ptr stackAlign arr sz
  pure (ArrayStack ptr arr, mem2)
