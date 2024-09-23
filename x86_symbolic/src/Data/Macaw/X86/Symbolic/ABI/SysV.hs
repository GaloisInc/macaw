{-|
Copyright        : (c) Galois, Inc 2024
Maintainer       : Langston Barrett <langston@galois.com>

On x86_64 with the SysV ABI, the stack grows \"downwards\" from high addresses
to low. The end of the stack is initialized with the ELF auxiliary vector (not
modelled here), and functions expect the following data to be available above
their stack frame (i.e., just above the address in @rsp@), from high addresses
to low:

* Padding (if necessary)
* Their stack-spilled arguments
* The return address

(The end of the stack-spilled argument list must be 16-byte aligned, which may
necessitate the use of padding, depending on the number of spilled arguments and
the layout of the caller\'s stack frame.)

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
|---------------------| <- %rsp + 8 (16-byte aligned)
| Return address      |
|---------------------| <- %rsp
| Callee's frame      |
|---------------------|

Low addresses
@

The functions in this module support manipulation of a stack under these
constraints. ABI-compatible machine code translated by Macaw manages the stack
for itself, so this module is primarily helpful for initial setup of the stack,
before starting symbolic execution.

Helpful links:

* <https://eli.thegreenplace.net/2011/09/06/stack-frame-layout-on-x86-64>
* <https://wiki.osdev.org/System_V_ABI#x86-64>
* <https://refspecs.linuxfoundation.org/elf/x86_64-abi-0.99.pdf>

This module is meant to be imported qualified.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Data.Macaw.X86.Symbolic.ABI.SysV
  ( StackPointer
  , getStackPointer
  , stackPointerReg
  , RetAddr(..)
  , freshRetAddr
  , alignStackPointer
  , SpilledArgs(..)
  , writeSpilledArgs
  , writeRetAddr
  , allocStackFrame
  , pushStackFrame
  , allocStack
  ) where

import Control.Lens qualified as Lens
import Data.BitVector.Sized qualified as BVS
import Data.Coerce (coerce)
import Data.Macaw.Symbolic qualified as MS
import Data.Macaw.Symbolic.Stack qualified as MSS
import Data.Macaw.X86 qualified as X86
import Data.Macaw.X86.Symbolic qualified as X86S
import Data.Parameterized.Classes (ixF')
import Data.Parameterized.Context qualified as Ctx
import Data.Sequence qualified as Seq
import Lang.Crucible.Backend qualified as C
import Lang.Crucible.LLVM.Bytes qualified as Bytes
import Lang.Crucible.LLVM.DataLayout qualified as CLD
import Lang.Crucible.LLVM.MemModel qualified as MM
import Lang.Crucible.Simulator qualified as C
import What4.Interface qualified as WI

-- | Helper, not exported
ptrBytes :: Integer
ptrBytes = 8

ptrRepr :: WI.NatRepr 64
ptrRepr = WI.knownNat

-- | A pointer to a SysV-compatible x86_64 stack
newtype StackPointer sym = StackPointer { getStackPointer :: MM.LLVMPtr sym 64 }

-- | A lens for accessing the stack pointer register as a 'StackPointer'
stackPointerReg ::
  Lens.Lens'
    (Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes X86.X86_64))
    (StackPointer sym)
stackPointerReg =
  Lens.lens
    (\regs -> StackPointer (C.unRV (regs Lens.^. ixF' X86S.rsp)))
    (\regs v -> regs Lens.& ixF' X86S.rsp Lens..~ C.RV (getStackPointer v))

-- | A return address
newtype RetAddr sym = RetAddr { getRetAddr :: MM.LLVMPtr sym 64 }

-- | Create a fresh, symbolic return address.
freshRetAddr :: C.IsSymInterface sym => sym -> IO (RetAddr sym)
freshRetAddr sym = do
  bv <- WI.freshConstant sym (WI.safeSymbol "x86_64_ret_addr") (WI.BaseBVRepr ptrRepr)
  ptr <- MM.llvmPointer_bv sym bv
  pure (RetAddr ptr)

-- | Align the stack pointer to a particular 'CLD.Alignment'.
alignStackPointer ::
  C.IsSymInterface sym =>
  sym ->
  CLD.Alignment ->
  StackPointer sym ->
  IO (StackPointer sym)
alignStackPointer = let ?ptrWidth = ptrRepr in coerce MSS.alignStackPointer

-- | Stack-spilled arguments, in normal order
newtype SpilledArgs sym
  = SpilledArgs { getSpilledArgs :: Seq.Seq (MM.LLVMPtr sym 64) }

-- | Write pointer-sized stack-spilled arguments to the stack.
--
-- SysV specifies that they will be written in reverse order, i.e., the last
-- element of the 'Seq.Seq' will be written to the highest address. It further
-- specifies that the end of the argument list will be 16-byte aligned. This
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
  let align8 = CLD.exponentToAlignment 3  -- 2^3 = 8
  coerce (MSS.writeSpilledArgs bak) mem align8 sp spilledArgs

-- | Write the return address to the stack.
--
-- Asserts that the stack allocation is writable and large enough to contain the
-- return address.
writeRetAddr ::
  C.IsSymBackend sym bak =>
  (?memOpts :: MM.MemOptions) =>
  MM.HasLLVMAnn sym =>
  bak ->
  MM.MemImpl sym ->
  StackPointer sym ->
  RetAddr sym ->
  IO (StackPointer sym, MM.MemImpl sym)
writeRetAddr bak mem sp retAddr = do
  let sym = C.backendGetSym bak
  let ?ptrWidth = MM.ptrWidth (getRetAddr retAddr)
  ptrSzBv <- WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth ptrBytes)
  top <- MM.ptrSub sym ?ptrWidth (getStackPointer sp) ptrSzBv
  let i64 = MM.bitvectorType (Bytes.toBytes (8 :: Int))
  let val = MM.ptrToPtrVal (getRetAddr retAddr)
  mem' <- MM.storeRaw bak mem top i64 CLD.noAlignment val
  pure (StackPointer top, mem')

-- | Allocate a single stack frame by decrementing the stack pointer.
--
-- From high to low addresses:
--
-- * First, write stack-spilled arguments in reverse order
-- * Then, write the return address
--
-- Asserts that the stack allocation is writable and large enough to contain the
-- spilled arguments and return address.
allocStackFrame ::
  C.IsSymBackend sym bak =>
  (?memOpts :: MM.MemOptions) =>
  MM.HasLLVMAnn sym =>
  bak ->
  MM.MemImpl sym ->
  StackPointer sym ->
  SpilledArgs sym ->
  RetAddr sym ->
  IO (StackPointer sym, MM.MemImpl sym)
allocStackFrame bak mem sp spilledArgs retAddr = do
  let ?ptrWidth = ptrRepr
  (sp', mem') <- writeSpilledArgs bak mem sp spilledArgs
  writeRetAddr bak mem' sp' retAddr

-- | Like 'allocStackFrame', but manipulates @rsp@ directly.
--
-- Asserts that the stack allocation is writable and large enough to contain the
-- spilled arguments and return address.
pushStackFrame ::
  C.IsSymBackend sym bak =>
  (?memOpts :: MM.MemOptions) =>
  MM.HasLLVMAnn sym =>
  bak ->
  MM.MemImpl sym ->
  -- | Assignment of values to registers
  Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes X86.X86_64) ->
  SpilledArgs sym ->
  RetAddr sym ->
  IO
    ( Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes X86.X86_64)
    , MM.MemImpl sym
    )
pushStackFrame bak mem regs spilledArgs retAddr = do
  let sp = regs Lens.^. stackPointerReg
  (sp', mem') <- allocStackFrame bak mem sp spilledArgs retAddr
  let regs' = regs Lens.& stackPointerReg Lens..~ sp'
  pure (regs', mem')

-- | Like 'MSS.createArrayStack', but puts the stack pointer in @rsp@ directly.
--
-- Does not allow allocating stack slots, use 'allocStackFrame' or
-- 'pushStackFrame' for that.
allocStack ::
  C.IsSymBackend sym bak =>
  (?memOpts :: MM.MemOptions) =>
  MM.HasLLVMAnn sym =>
  bak ->
  MM.MemImpl sym ->
  -- | Assignment of values to registers
  Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes X86.X86_64) ->
  -- | Size of stack allocation
  WI.SymExpr sym (WI.BaseBVType 64) ->
  IO
    ( Ctx.Assignment (C.RegValue' sym) (MS.MacawCrucibleRegTypes X86.X86_64)
    , MM.MemImpl sym
    )
allocStack bak mem regs sz = do
  let ?ptrWidth = ptrRepr
  let slots = MSS.ExtraStackSlots 0
  (MSS.ArrayStack _base top _arr, mem') <- MSS.createArrayStack bak mem slots sz
  let regs' = regs Lens.& stackPointerReg Lens..~ StackPointer top
  pure (regs', mem')
