{-|
Copyright        : (c) Galois, Inc 2024
Maintainer       : Langston Barrett <langston@galois.com>

On x86_64 with the SysV ABI, the stack grows \"downwards\" from high addresses
to low. The end of the stack is initialized with the ELF auxiliary vector (not
modelled here), and functions expect the following data to be available above
their stack frame (i.e., just above the address in @rsp@), from high addresses
to low:

* Their stack-spilled arguments
* The return address

The functions in this module support manipulation of a stack under these
constraints. ABI-compatible machine code translated by Macaw manages the stack
for itself, so this module is primarily helpful for initial setup of the stack,
before starting symbolic execution.

Helpful links:

* <https://eli.thegreenplace.net/2011/09/06/stack-frame-layout-on-x86-64>
* <https://wiki.osdev.org/System_V_ABI#x86-64>

TODO: The stack is supposed to be 16-byte aligned before a @call@.

This module is meant to be imported qualified.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}

module Data.Macaw.X86.Symbolic.ABI.SysV
  ( StackPointer
  , getStackPointer
  , RetAddr(..)
  , freshRetAddr
  , writeSpilledArgs
  , writeRetAddr
  , allocStackFrame
  ) where

-- TODO: sort me!
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.LLVM.MemModel as MM
import qualified Data.Sequence as Seq
import qualified What4.Interface as WI
import qualified Data.BitVector.Sized as BVS
import qualified Lang.Crucible.LLVM.Bytes as Bytes
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Control.Monad as Monad

-- | Helper, not exported
ptrBytes :: Integer
ptrBytes = 8

ptrRepr :: WI.NatRepr 64
ptrRepr = WI.knownNat

-- | A pointer to a SysV-compatible x86_64 stack
newtype StackPointer sym = StackPointer { getStackPointer :: MM.LLVMPtr sym 64 }

-- | A return address
newtype RetAddr sym = RetAddr { getRetAddr :: MM.LLVMPtr sym 64 }

-- | Create a fresh, symbolic return address
freshRetAddr :: C.IsSymInterface sym => sym -> IO (RetAddr sym)
freshRetAddr sym = do
  bv <- WI.freshConstant sym (WI.safeSymbol "x86_64_ret_addr") (WI.BaseBVRepr ptrRepr)
  ptr <- MM.llvmPointer_bv sym bv
  pure (RetAddr ptr)

-- | Write pointer-sized stack-spilled arguments to the stack.
--
-- SysV specifies that they will be written in reverse order, i.e., the last
-- element of the 'Seq.Seq' will be written to the highest address.
writeSpilledArgs ::
  C.IsSymBackend sym bak =>
  (?memOpts :: MM.MemOptions) =>
  MM.HasLLVMAnn sym =>
  bak ->
  MM.MemImpl sym ->
  StackPointer sym ->
  -- | Stack-spilled arguments, in normal order
  Seq.Seq (MM.LLVMPtr sym 64) ->
  IO (StackPointer sym, MM.MemImpl sym)
writeSpilledArgs bak mem sp spilledArgs = do
  let sym = C.backendGetSym bak
  eight <- WI.bvLit sym ptrRepr (BVS.mkBV WI.knownNat 8)
  let i64 = MM.bitvectorType (Bytes.toBytes (64 :: Int))
  let ?ptrWidth = ptrRepr
  let writeWord (StackPointer p, m) arg = do
        p' <- MM.ptrSub sym ?ptrWidth p eight
        m' <- MM.storeRaw bak m p' i64 CLD.noAlignment (MM.ptrToPtrVal arg)
        pure (StackPointer p', m')
  Monad.foldM writeWord (sp, mem) (Seq.reverse spilledArgs)

-- | Write the return address to the stack.
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
  let i64 = MM.bitvectorType (Bytes.toBytes (64 :: Int))
  let val = MM.ptrToPtrVal (getRetAddr retAddr)
  mem' <- MM.storeRaw bak mem top i64 CLD.noAlignment val
  pure (StackPointer top, mem')

-- | Allocate a single stack frame by decrementing the stack pointer.
--
-- From high to low addresses:
--
-- * First, write stack-spilled arguments in reverse order
-- * Then, write the return address
allocStackFrame ::
  C.IsSymBackend sym bak =>
  (?memOpts :: MM.MemOptions) =>
  MM.HasLLVMAnn sym =>
  bak ->
  MM.MemImpl sym ->
  StackPointer sym ->
  -- | Stack-spilled arguments, in normal order
  Seq.Seq (MM.LLVMPtr sym 64) ->
  RetAddr sym ->
  IO (StackPointer sym, MM.MemImpl sym)
allocStackFrame bak mem sp spilledArgs retAddr = do
  let ?ptrWidth = ptrRepr
  (sp', mem') <- writeSpilledArgs bak mem sp spilledArgs
  writeRetAddr bak mem' sp' retAddr

-- TODO: Pushing a stack frame (i.e., manipulating rsp)
-- TODO: Extracting the stack pointer from registers
-- TODO: Allocating the stack
