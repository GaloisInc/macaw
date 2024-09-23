{-|
Copyright        : (c) Galois, Inc 2024
Maintainer       : Langston Barrett <langston@galois.com>

On AArch32, the stack grows \"downwards\" from high addresses to low. The end
of the stack is initialized with the ELF auxiliary vector (not modelled here),
and functions expect the following data to be available above their stack frame
(i.e., just above the address in @sp@/@r13@), from high addresses to low:

* Padding (if necessary)
* Their stack-spilled arguments

The stack is always 4-byte aligned, and must be 8-byte aligned \"at any public
interface\", i.e., at function calls.

Unlike x86_64, the return address is not stored on the stack.

The following diagram summarizes the stack frame layout:

@
High addresses

|---------------------|
| Caller's frame      |
|---------------------|
| Padding (if needed) |
|---------------------|
| Spilled argument n  |
|---------------------|
| ...                 |
|---------------------|
| Spilled argument 2  |
|---------------------|
| Spilled argument 1  |
|---------------------| <- sp
| Callee's frame      |
|---------------------|

Low addresses
@

The functions in this module support manipulation of a stack under these
constraints. ABI-compatible machine code translated by Macaw manages the stack
for itself, so this module is primarily helpful for initial setup of the stack,
before starting symbolic execution.

Helpful links:

* <https://github.com/ARM-software/abi-aa/blob/a82eef0433556b30539c0d4463768d9feb8cfd0b/aapcs32/aapcs32.rst#621the-stack>
* <https://learn.microsoft.com/en-us/cpp/build/overview-of-arm-abi-conventions?view=msvc-170>

This module is meant to be imported qualified.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Data.Macaw.AArch32.Symbolic.ABI
  ( StackPointer
  , getStackPointer
  , stackPointerReg
  , alignStackPointer
  , SpilledArgs(..)
  , writeSpilledArgs
  , pushStackFrame
  , allocStack
  ) where

import Control.Lens qualified as Lens
import Data.BitVector.Sized qualified as BVS
import Data.Coerce (coerce)
import Data.Macaw.AArch32.Symbolic qualified as AArch32S
import Data.Macaw.ARM qualified as AArch32
import Data.Macaw.Symbolic qualified as MS
import Data.Macaw.Symbolic.Stack qualified as MSS
import Data.Parameterized.Classes (ixF')
import Data.Parameterized.Context qualified as Ctx
import Data.Sequence qualified as Seq
import GHC.Natural (naturalToInteger)
import Lang.Crucible.Backend qualified as C
import Lang.Crucible.LLVM.DataLayout qualified as CLD
import Lang.Crucible.LLVM.MemModel qualified as MM
import Lang.Crucible.Simulator qualified as C
import What4.Interface qualified as WI

-- | Helper, not exported
ptrRepr :: WI.NatRepr 32
ptrRepr = WI.knownNat

-- | A pointer to an AArch32 stack
newtype StackPointer sym = StackPointer { getStackPointer :: MM.LLVMPtr sym 32 }

-- | A lens for accessing the stack pointer register as a 'StackPointer'
stackPointerReg ::
  Lens.Lens'
    (Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes AArch32.ARM))
    (StackPointer sym)
stackPointerReg =
  Lens.lens
    (\regs -> StackPointer (C.unRV (regs Lens.^. ixF' AArch32S.sp)))
    (\regs v -> regs Lens.& ixF' AArch32S.sp Lens..~ C.RV (getStackPointer v))

-- | Align the stack pointer to a particular 'CLD.Alignment'.
alignStackPointer ::
  C.IsSymInterface sym =>
  sym ->
  CLD.Alignment ->
  StackPointer sym ->
  IO (StackPointer sym)
alignStackPointer sym align orig@(StackPointer (MM.LLVMPointer blk off)) = do
  let alignInt = 2 ^ naturalToInteger (CLD.alignmentToExponent align)
  if alignInt == 1
  then pure orig
  else do
    -- Because the stack grows down, we can align it by simply ANDing the stack
    -- pointer with a mask with some amount of 1s followed by some amount of 0s.
    let mask = BVS.complement ptrRepr (BVS.mkBV ptrRepr (alignInt - 1))
    maskBv <- WI.bvLit sym ptrRepr mask
    off' <- WI.bvAndBits sym off maskBv
    pure (StackPointer (MM.LLVMPointer blk off'))

-- | Stack-spilled arguments, in normal order
newtype SpilledArgs sym
  = SpilledArgs { getSpilledArgs :: Seq.Seq (MM.LLVMPtr sym 32) }

-- | Write pointer-sized stack-spilled arguments to the stack.
--
-- The ABI specifies that they will be written in reverse order, i.e., the last
-- element of the 'Seq.Seq' will be written to the highest address. It further
-- specifies that the end of the argument list will be 8-byte aligned. This
-- function will allocate additional stack space before the spilled arguments if
-- necessary to establish this constraint.
--
-- Asserts that the stack allocation is writable and large enough to contain the
-- spilled arguments.
writeSpilledArgs ::
  C.IsSymBackend sym bak =>
  (?memOpts :: MM.MemOptions) =>
  MM.HasLLVMAnn sym =>
  bak ->
  MM.MemImpl sym ->
  StackPointer sym ->
  SpilledArgs sym ->
  IO (StackPointer sym, MM.MemImpl sym)
writeSpilledArgs bak mem sp spilledArgs = do
  let ?ptrWidth = ptrRepr
  let align4 = CLD.exponentToAlignment 2  -- 2^2 = 4
  coerce (MSS.writeSpilledArgs bak) mem align4 sp spilledArgs

-- | Like 'writeSpilledArgs', but manipulates @sp@ directly.
--
-- Asserts that the stack allocation is writable and large enough to contain the
-- spilled arguments.
pushStackFrame ::
  C.IsSymBackend sym bak =>
  (?memOpts :: MM.MemOptions) =>
  MM.HasLLVMAnn sym =>
  bak ->
  MM.MemImpl sym ->
  -- | Assignment of values to registers
  Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes AArch32.ARM) ->
  SpilledArgs sym ->
  IO
    ( Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes AArch32.ARM)
    , MM.MemImpl sym
    )
pushStackFrame bak mem regs spilledArgs = do
  let sp = regs Lens.^. stackPointerReg
  (sp', mem') <- writeSpilledArgs bak mem sp spilledArgs
  let regs' = regs Lens.& stackPointerReg Lens..~ sp'
  pure (regs', mem')

-- | Like 'MSS.createArrayStack', but puts the stack pointer in @sp@ directly.
--
-- Does not allow allocating stack slots, use 'pushStackFrame' for that.
allocStack ::
  C.IsSymBackend sym bak =>
  (?memOpts :: MM.MemOptions) =>
  MM.HasLLVMAnn sym =>
  bak ->
  MM.MemImpl sym ->
  -- | Assignment of values to registers
  Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes AArch32.ARM) ->
  -- | Size of stack allocation
  WI.SymExpr sym (WI.BaseBVType 32) ->
  IO
    ( Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes AArch32.ARM)
    , MM.MemImpl sym
    )
allocStack bak mem regs sz = do
  let ?ptrWidth = ptrRepr
  let slots = MSS.ExtraStackSlots 0
  (MSS.ArrayStack _base top _arr, mem') <- MSS.createArrayStack bak mem slots sz
  let regs' = regs Lens.& stackPointerReg Lens..~ StackPointer top
  pure (regs', mem')
