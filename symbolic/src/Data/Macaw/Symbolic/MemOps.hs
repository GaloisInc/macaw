-- This module deals with the fact that a number of operations work differently,
-- depending on if they are applied to pointers or bit-vectors.
{-# LANGUAGE ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language FlexibleContexts #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language ImplicitParams #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language TypeApplications #-}
{-# Language PatternGuards #-}
module Data.Macaw.Symbolic.MemOps
  ( PtrOp
  , GlobalMap(..)
  , doPtrAdd
  , doPtrSub
  , doPtrMux
  , doPtrEq
  , doPtrLt
  , doPtrLeq
  , doPtrAnd
  , doPtrXor
  , doPtrTrunc
  , doPtrUExt
  , doReadMem
  , doCondReadMem
  , doWriteMem
  , doCondWriteMem
  , doGetGlobal
  , doLookupFunctionHandle
  , doPtrToBits
  , getMem
  , setMem
  , tryGlobPtr
  , Regs
  , MacawSimulatorState(..)
  , LookupFunctionHandle(..)
  , LookupSyscallHandle(..)
  , ptrOp
  , isValidPtr
  , mkUndefinedBool
  ) where

import           Control.Exception (throwIO)
import           Control.Lens ((^.),(&),(%~))
import           Control.Monad (guard, when)
import           Data.Bits (testBit)
import qualified Data.Vector as V

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized (Some(..))
import qualified Data.Parameterized.Context as Ctx


import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common (GlobalVar)
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.Simulator.RegMap as C
import           Lang.Crucible.Simulator.ExecutionTree
          ( CrucibleState, stateSymInterface, stateContext
          , stateTree, actFrame, gpGlobals, withBackend
          )
import           Lang.Crucible.Simulator.GlobalState (lookupGlobal,insertGlobal)
import           Lang.Crucible.Simulator.Intrinsics (GetIntrinsic, Intrinsic)
import           Lang.Crucible.Simulator.RegMap (RegEntry,regValue)
import           Lang.Crucible.Simulator.RegValue (RegValue)
import           Lang.Crucible.Simulator.SimError (SimErrorReason(AssertFailureSimError))
import           Lang.Crucible.Types

import           Lang.Crucible.LLVM.MemModel
          ( Mem, MemImpl, LLVMPointerType, LLVMPtr, isValidPointer, memEndian
          , llvmPointerView, muxLLVMPtr, llvmPointer_bv, ptrAdd, ptrSub, ptrEq
          )
import qualified Lang.Crucible.LLVM.MemModel as Mem
import qualified Lang.Crucible.LLVM.MemModel.Generic as Mem.G

import           Lang.Crucible.LLVM.DataLayout (Alignment, EndianForm(..), noAlignment, exponentToAlignment)
import           Lang.Crucible.LLVM.Bytes (Bytes(..))

import           Data.Macaw.Symbolic.CrucGen (addrWidthIsPos, ArchRegStruct, MacawExt, MacawCrucibleRegTypes)
import           Data.Macaw.Symbolic.PersistentState (ToCrucibleType)
import           Data.Macaw.CFG.Core (MemRepr(..))
import qualified Data.Macaw.CFG as M

infix 0 ~>

(~>) :: a -> b -> (a,b)
x ~> y = (x,y)

-- | The offset part of a pointer.
asBits :: LLVMPtr sym w -> RegValue sym (BVType w)
asBits = snd . llvmPointerView

-- | The base part of a pointer.
ptrBase :: LLVMPtr sym w -> RegValue sym NatType
ptrBase = fst . llvmPointerView

-- | The 'GlobalMap' is a function that maps from (possibly segmented) program
-- virtual addresses into pointers into the LLVM memory model heap (the
-- 'LLVMPtr' type).
--
-- There are two types of value translated here:
--
-- 1. Bitvectors treated as pointers, and
-- 2. Segmented addresses (e.g., from object files or shared libraries)
--
-- To set up the memory model to verify parts of a program, callers need to
-- allocate regions of memory to store data including the initial program state.
-- The user-facing API for allocating memory is the 'doMalloc' primitive from
-- Lang.Crucible.LLVM.MemModel.  This allocates fresh memory that is distinct
-- from all other memory in the system.  The distinctness is guaranteed because
-- each allocation has a unique region identifier.  Each freshly allocated
-- region of memory has a base address of zero and a size.
--
-- In a machine code program, there are a few different kinds of memory to map
-- into the address space: 1) a *stack*, 2) the *data* segment, 3) and the
-- program *text* segment.
--
-- The *stack* should be logically separate from everything else, so an
-- allocation with 'doMalloc' is natural.  It is the responsibility of the
-- caller to place the pointer to the stack (that is the LLVM memory model
-- pointer) into the appropriate register in the machine state for their
-- architecture.
--
-- The *data* and *text* segments are static data in the original binary image
-- being analyzed.  They are usually disjoint, so it usually makes sense to
-- allocate one region of memory for each one using 'doMalloc'.  To resolve a
-- computed address (which will be a bitvector, i.e., an LLVMPtr value with a
-- zero region index) that refers to either, a typical workflow in the
-- 'GlobalMap' function is:
--
-- 1. Inspect the region index (the @'RegValue' sym 'NatType'@ parameter)
-- 2. If the region index is zero, it is a bitvector to translate into an
--    LLVM memory model pointer ('LLVMPtr')
-- 3. Look up the offset of the pointer from zero (the @'RegValue' sym ('BVType'
--    w)@) in a map (probably an IntervalMap); that map should return the base
--    address of the allocation (which is an 'LLVMPtr')
-- 4. Depending on the representation of that pointer chosen by the
--    frontend/setup code, the 'LLVMPtr' may need to be corrected to rebase it,
--    as the segment being represented by that allocation may not actually start
--    at address 0 (while the LLVM offset does start at 0).
--
-- That discussion describes the translation of raw bitvectors into pointers.
-- This mapping is also used in another case (see 'doGetGlobal'): translating
-- the address of a relocatable value (which doesn't necessarily have a
-- well-defined absolute address) into an address in the LLVM memory model.
-- Relocatable values in this setting have a non-zero region index as an input.
-- The 'GlobalMap' is responsible for 1) determining which LLVM allocation
-- contains the relocatable value, and 2) returning the corresponding address in
-- that allocation.
newtype GlobalMap sym mem w =
  GlobalMap
  { applyGlobalMap ::
      forall bak. IsSymBackend sym bak =>
       bak                        {- The symbolic backend -} ->
       GetIntrinsic sym mem       {- The global handle to the memory model -} ->
       RegValue sym NatType       {- The region index of the pointer being translated -} ->
       RegValue sym (BVType w)    {- The offset of the pointer into the region -} ->
       IO (LLVMPtr sym w)
  }

{- | Every now and then we encounter memory operations that
just read/write to some constant.  Normally, we do not allow
such things as we want memory to be allocated first.
However we need to make an exception for globals.
So, if we ever try to manipulate memory at some address
which is statically known to be a constant, we consult
the global map to see if we know about a correpsonding
address.  If so, we use that for the memory operation.

See the documentation of 'GlobalMap' for details about how that translation can
be handled.
-}
tryGlobPtr ::
  (IsSymBackend sym bak) =>
  bak ->
  RegValue sym Mem ->
  GlobalMap sym Mem w ->
  LLVMPtr sym w ->
  IO (LLVMPtr sym w)
tryGlobPtr bak mem mapBVAddress val
  | Just blockId <- asNat (ptrBase val)
  , blockId /= 0 = do
      -- If we know that the blockId is concretely not zero, the pointer is
      -- already translated into an LLVM pointer and can be passed through.
      return val
  | otherwise = do
      -- If the blockId is zero, we have to translate it into a proper LLVM
      -- pointer
      --
      -- Otherwise, the blockId is symbolic and we need to create a mux that
      -- conditionally performs the translation.
      applyGlobalMap mapBVAddress bak mem (ptrBase val) (asBits val)

-- | This is the form of binary operation needed by the simulator.
-- Note that even though the type suggests that we might modify the
-- state, we don't actually do it.
type PtrOp sym w a =
  forall s ext rtp blocks r ctx.
  IsSymInterface sym =>
  CrucibleState s sym ext rtp blocks r ctx {- ^ Simulator state   -} ->
  GlobalVar Mem                            {- ^ Memory model      -} ->
  M.AddrWidthRepr w                        {- ^ Width of pointer  -} ->
  RegEntry sym (LLVMPointerType w)         {- ^ Argument 1        -} ->
  RegEntry sym (LLVMPointerType w)         {- ^ Argument 2        -} ->
  IO (a, CrucibleState s sym ext rtp blocks r ctx)

-- | Get the current model of the memory.
getMem :: CrucibleState s sym ext rtp blocks r ctx ->
          GlobalVar (IntrinsicType nm args) ->
          IO (Intrinsic sym nm args)
getMem st mvar =
  case lookupGlobal mvar (st ^. stateTree . actFrame . gpGlobals) of
    Just mem -> return mem
    Nothing  -> fail ("Global heap value not initialized: " ++ show mvar)

setMem :: CrucibleState s sym ext rtp blocks r ctx ->
          GlobalVar (IntrinsicType nm args) ->
          Intrinsic sym nm args ->
          CrucibleState s sym ext rtp blocks r ctx
setMem st mvar mem =
  st & stateTree . actFrame . gpGlobals %~ insertGlobal mvar mem

-- | Classify the arguments, and continue.
--
-- This combinator takes a continuation that is provided a number of (SMT)
-- /predicates/ that classify the inputs as bitvectors or pointers.  An
-- 'LLVMPtr' is a bitvector if its region id (base) is zero.
ptrOp ::
  ( forall bak.
    (IsSymBackend sym bak, (1 <= w)) =>
    bak ->
    RegValue sym Mem ->
    M.AddrWidthRepr w ->
    Pred sym -> Pred sym -> Pred sym -> Pred sym ->
    LLVMPtr sym w -> LLVMPtr sym w -> IO a
  ) ->
  PtrOp sym w a
ptrOp k st mvar w x0 y0 =
  withBackend (st^.stateContext) $ \bak ->
  do mem <- getMem st mvar
     LeqProof <- return (addrWidthIsPos w)
     let sym = backendGetSym bak
         x   = regValue x0
         y   = regValue y0

     zero <- natLit sym 0

     xBits <- natEq sym (ptrBase x) zero
     xPtr <- notPred sym xBits

     yBits <- natEq sym (ptrBase y) zero
     yPtr <- notPred sym yBits

     a <- k bak mem w xPtr xBits yPtr yBits x y
     return (a,st)

type PtrOpNR sym w a =
  forall s ext rtp blocks r ctx.
  (IsSymInterface sym, 1 <= w) =>
  CrucibleState s sym ext rtp blocks r ctx {- ^ Simulator state   -} ->
  GlobalVar Mem                            {- ^ Memory model      -} ->
  NatRepr w                                {- ^ Width of pointer  -} ->
  RegEntry sym (LLVMPointerType w)         {- ^ Argument 1        -} ->
  RegEntry sym (LLVMPointerType w)         {- ^ Argument 2        -} ->
  IO (a, CrucibleState s sym ext rtp blocks r ctx)


-- 'ptrOp' in terms of a 'NatRepr' instead of an 'M.AddrWidthRepr'
--
-- The 'M.AddrWidthRepr' is too restrictive for some operations (e.g., larger
-- than pointer-width ops)
ptrOpNR ::
  ( forall bak. (IsSymBackend sym bak, 1 <= w) =>
    bak ->
    RegValue sym Mem ->
    NatRepr w ->
    Pred sym -> Pred sym -> Pred sym -> Pred sym ->
    LLVMPtr sym w -> LLVMPtr sym w -> IO a
  ) ->
  PtrOpNR sym w a
ptrOpNR k st mvar w x0 y0 =
  withBackend (st^.stateContext) $ \bak ->
  do mem <- getMem st mvar
     let sym = backendGetSym bak
         x   = regValue x0
         y   = regValue y0

     zero <- natLit sym 0

     xBits <- natEq sym (ptrBase x) zero
     xPtr <- notPred sym xBits

     yBits <- natEq sym (ptrBase y) zero
     yPtr <- notPred sym yBits

     a <- k bak mem w xPtr xBits yPtr yBits x y
     return (a,st)


mkUndefined ::
  (IsSymInterface sym) =>
  sym -> String -> BaseTypeRepr t -> IO (RegValue sym (BaseToType t))
mkUndefined sym unm ty =
  do let name = "undefined_" ++ unm
         nm   = safeSymbol name
     freshConstant sym nm ty

-- | A fresh bit-vector variable
mkUndefinedBV ::
  (IsSymInterface sym, 1 <= w) =>
  sym -> String -> NatRepr w -> IO (RegValue sym (BVType w))
mkUndefinedBV sym nm w =
  mkUndefined sym (nm ++ "bv" ++ show w ++ "_") (BaseBVRepr w)

mkUndefinedNat ::
  (IsSymInterface sym) => sym -> String -> IO (RegValue sym NatType)
mkUndefinedNat sym unm =
  do let name = "undefined_" ++ unm
         nm   = safeSymbol name
     freshNat sym nm

-- | A fresh boolean variable
mkUndefinedBool ::
  (IsSymInterface sym) => sym -> String -> IO (RegValue sym BoolType)
mkUndefinedBool sym nm =
  mkUndefined sym (nm ++ "bool_") BaseBoolRepr

mkUndefinedPtr :: (IsSymInterface sym, 1 <= w) =>
  sym -> String -> NatRepr w -> IO (LLVMPtr sym w)
mkUndefinedPtr sym nm w =
  do base <- mkUndefinedNat sym ("ptr_base_" ++ nm)
     off  <- mkUndefinedBV sym ("ptr_offset_" ++ nm) w
     return (Mem.LLVMPointer base off)

-- | This is called whenever a (bit-vector/pointer) is used as a bit-vector.
-- The result is undefined (i.e., a fresh unknown value) if it is given
-- a real pointer.
doPtrToBits ::
  (IsSymInterface sym, 1 <= w) =>
  sym ->
  LLVMPtr sym w ->
  IO (SymBV sym w)
doPtrToBits sym (Mem.LLVMPointer base off) =
  do undef <- mkUndefinedBV sym "ptr_to_bits" (bvWidth off)
     notPtr <- natEq sym base =<< natLit sym 0
     bvIte sym notPtr off undef

-- | The state extension for Crucible holding Macaw-specific state
--
-- Currently, evaluation of Macaw doesn't require anything extra from the
-- simulator.  We use a distinct type here for forward-compatibility.
data MacawSimulatorState sym = MacawSimulatorState

type Regs sym arch = Ctx.Assignment (C.RegValue' sym)
                                    (MacawCrucibleRegTypes arch)

-- | A function to inspect a machine state and translate it into a 'C.FnHandle'
-- corresponding to the function that the simulator should call
--
-- The function takes a full machine state (register state and memory) and
-- inspects it (likely by looking at the current value of the machine
-- instruction pointer) to determine which function the simulator would jump to
-- if the next Crucible statement was a call.
--
-- The callback additionally takes a full 'CrucibleState' and returns an updated
-- 'CrucibleState' to allow the callback to lazily instantiate callees (e.g., by
-- constructing the CFG of the callee on the fly) and register them with the
-- simulator.
newtype LookupFunctionHandle sym arch = LookupFunctionHandle
     (forall rtp blocks r ctx p
   . CrucibleState p sym (MacawExt arch) rtp blocks r ctx
  -> MemImpl sym
  -> Ctx.Assignment (C.RegValue' sym) (MacawCrucibleRegTypes arch)
  -> IO (C.FnHandle (Ctx.EmptyCtx Ctx.::> ArchRegStruct arch) (ArchRegStruct arch), CrucibleState p sym (MacawExt arch) rtp blocks r ctx))

-- | A function to inspect the machine state and translate it into a
-- 'C.FnHandle' corresponding to the system call model that the simulator should
-- call.
--
-- This function takes a subset of machine state determined by the ABI of the
-- system being simulated. This could be an entire register state, but need not
-- be. It could also include additional values (e.g., immediate operands to a
-- syscall instruction).
--
-- Compared to 'LookupFunctionHandle', this function also takes a sequence of
-- type reprs that indicate the return values that are returned by the syscall
-- model.
--
-- Note that all of the arguments passed to this lookup function are also passed
-- to the system call (reflected in the types of the function handle
-- returned). Note that it is the responsibility of the architecture-specific
-- backend (e.g., macaw-x86) to ensure that the returned values are placed in
-- the appropriate machine registers.
newtype LookupSyscallHandle sym arch =
  LookupSyscallHandle (  forall rtp blocks r ctx atps rtps p
                      .  Ctx.Assignment TypeRepr atps
                      -> Ctx.Assignment TypeRepr rtps
                      -> CrucibleState p sym (MacawExt arch) rtp blocks r ctx
                      -> C.RegEntry sym (StructType atps)
                      -> IO (C.FnHandle atps (StructType rtps), CrucibleState p sym (MacawExt arch) rtp blocks r ctx)
                      )

--------------------------------------------------------------------------------
doLookupFunctionHandle :: (IsSymInterface sym)
                       => (CrucibleState s sym ext trp blocks r ctx -> MemImpl sym -> regs -> IO (a, CrucibleState s sym ext trp blocks r ctx))
                       -> CrucibleState s sym ext trp blocks r ctx
                       -> GlobalVar Mem
                       -> regs
                       -> IO (a, CrucibleState s sym ext trp blocks r ctx)
doLookupFunctionHandle k st mvar regs = do
  mem <- getMem st mvar
  k st mem regs
--------------------------------------------------------------------------------



addrWidthAtLeast16 :: M.AddrWidthRepr w -> LeqProof 16 w
addrWidthAtLeast16 M.Addr32 = LeqProof
addrWidthAtLeast16 M.Addr64 = LeqProof

doGetGlobal ::
  (IsSymInterface sym, M.MemWidth w) =>
  CrucibleState s sym ext rtp blocks r ctx {- ^ Simulator state   -} ->
  GlobalVar (IntrinsicType nm args)        {- ^ Model of memory   -} ->
  GlobalMap sym (IntrinsicType nm args) w ->
  M.MemAddr w                              {- ^ Address identifier -} ->
  IO ( RegValue sym (LLVMPointerType w)
     , CrucibleState s sym ext rtp blocks r ctx
     )
doGetGlobal st mvar globs addr =
  withBackend (st^.stateContext) $ \bak -> do
    let sym = backendGetSym bak
    mem <- getMem st mvar
    regionNum <- natLit sym (fromIntegral (M.addrBase addr))
    let w = M.addrWidthNatRepr (M.addrWidthRepr addr)
    offset <- bvLit sym w (BV.mkBV w (M.memWordToUnsigned (M.addrOffset addr)))
    ptr <- applyGlobalMap globs bak mem regionNum offset
    return (ptr, st)

--------------------------------------------------------------------------------

binOpLabel :: IsSymInterface sym =>
  String -> LLVMPtr sym w -> LLVMPtr sym w -> String
binOpLabel lab x y =
  unlines [ "{ instruction: " ++ lab
          , ", operand 1:   " ++ show (Mem.ppPtr x)
          , ", operand 2:   " ++ show (Mem.ppPtr y)
          , "}"
          ]

check :: (IsSymBackend sym bak) => bak -> Pred sym -> String -> String -> IO ()
check bak valid name msg = assert bak valid
                    $ AssertFailureSimError errMsg errMsg
  where
    errMsg = "[" ++ name ++ "] " ++ msg

-- | Define an operation by cases.
--
-- NOTE that the cases defined using this combinator do not need to be complete;
-- it adds a fallthrough case that asserts false (indicating that it should be
-- impossible)
cases ::
  (IsSymBackend sym bak) =>
  bak         {- ^ Simulator -} ->
  String      {- ^ Name of operation (for assertions) -} ->
  (sym -> Pred sym -> a -> a -> IO a) {- Mux results -} ->
  Maybe a           {- ^ Default: use this if none of the cases matched -} ->

  [(Pred sym,  IO ([(Pred sym,String)], a))]
    {- ^ Cases: (predicate when valid, result + additional checks) -} ->
  IO a
cases bak name mux def opts =
  case def of
    Just _ -> combine =<< mapM doCase opts
    Nothing ->
      do ok <- oneOf (map fst opts)
         check bak ok name ("Invalid arguments for " ++ show name)
         combine =<< mapM doCase opts
  where
  sym = backendGetSym bak

  oneOf xs =
    case xs of
      []     -> return (falsePred sym) -- shouldn't happen
      [p]    -> return p
      p : ps -> orPred sym p =<< oneOf ps

  combine [] = fail "[bug] Empty cases"
  combine [(p,a)] = case def of
                      Just d  -> mux sym p a d
                      Nothing -> return a
  combine ((p,a) : more) = mux sym p a =<< combine more

  doCase (p,m) =
    do (checks,a) <- m
       mapM_ (subCheck p) checks
       return (p,a)

  subCheck cp (p,msg) =
    do valid <- impliesPred sym cp p
       check bak valid name msg

endCase :: Monad m => a -> m ([b],a)
endCase r = return ([],r)

endCaseCheck :: Monad m => a -> b -> c -> m ([(a,b)],c)
endCaseCheck a b c = return ([(a,b)],c)

isValidPtr ::
  (IsSymInterface sym) =>
  sym ->
  MemImpl sym ->
  M.AddrWidthRepr w ->
  LLVMPtr sym w ->
  IO (Pred sym)
isValidPtr sym mem w p =
 do LeqProof <- pure $ addrWidthIsPos w
    LeqProof <- pure $ addrWidthAtLeast16 w
    let ?ptrWidth = M.addrWidthNatRepr w
    isValidPointer sym p mem

isNullPtr ::
  (IsSymInterface sym) =>
  sym ->
  M.AddrWidthRepr w ->
  LLVMPtr sym w ->
  IO (Pred sym)
isNullPtr sym w p =
 do LeqProof <- pure $ addrWidthIsPos w
    LeqProof <- pure $ addrWidthAtLeast16 w
    let ?ptrWidth = M.addrWidthNatRepr w
    Mem.ptrIsNull sym Mem.PtrWidth p

doPtrMux :: Pred sym -> PtrOp sym w (LLVMPtr sym w)
doPtrMux c = ptrOp $ \bak _ w xPtr xBits yPtr yBits x y ->
  do let sym = backendGetSym bak
     both_bits <- andPred sym xBits yBits
     both_ptrs <- andPred sym xPtr  yPtr
     undef     <- mkUndefinedPtr sym "ptr_mux" (M.addrWidthNatRepr w)
     cases bak (binOpLabel "ptr_mux" x y) muxLLVMPtr (Just undef)
       [ both_bits ~>
           endCase =<< llvmPointer_bv sym =<< bvIte sym c (asBits x) (asBits y)
       , both_ptrs ~>
           endCase =<< muxLLVMPtr sym c x y
       ]

-- | Implementation of addition of two 'LLVMPtr's
--
-- The translation uses the 'LLVMPtr' type for both bitvectors and pointers, as
-- they are mostly indistinguishable at the machine code level (until they are
-- actually used as a pointer).  This operation looks a bit complicated because
-- there are four possible cases:
--
-- * Adding a pointer to a bitvector
-- * Adding a bitvector to a pointer
-- * Adding two bitvectors
-- * Adding two pointers (not allowed)
--
-- Note that the underlying pointer addition primitive from crucible-llvm,
-- 'ptrAdd', only accepts its operands in one order: pointer and then bitvector.
-- The cases below rearrange the operands as necessary.
--
-- The final case, of adding two bitvectors together, is also special cased
-- here.  NOTE that we do not do the tests at symbolic execution time: instead,
-- we generate a formula that encodes the necessary tests (hence the 'cases'
-- combinator).
--
-- NOTE that the case of adding two pointers is not explicitly addressed in the
-- 'cases' call below; 'cases' adds a fallthrough that asserts false.
doPtrAdd :: PtrOpNR sym w (LLVMPtr sym w)
doPtrAdd = ptrOpNR $ \bak _ w xPtr xBits yPtr yBits x y ->
  do let sym = backendGetSym bak
     both_bits <- andPred sym xBits yBits
     ptr_bits  <- andPred sym xPtr  yBits
     bits_ptr  <- andPred sym xBits yPtr
     a <- cases bak (binOpLabel "ptr_add" x y) muxLLVMPtr Nothing
       [ both_bits ~>
           endCase =<< llvmPointer_bv sym =<< bvAdd sym (asBits x) (asBits y)

       , ptr_bits ~> endCase =<< ptrAdd sym w x (asBits y)
       , bits_ptr ~> endCase =<< ptrAdd sym w y (asBits x)
       ]
     return a

-- | Implementation of subtraction of 'LLVMPtr's
--
-- This case is substantially similar to 'doPtrAdd', except the operation matrix
-- is:
--
-- * Subtracting a pointer from a bitvector (not allowed)
-- * Subtracting a bitvector from a pointer
-- * Subtracting two bitvectors
-- * Subtracting two pointers
--
-- Note that subtracting two pointers is allowed if (and only if) they are
-- pointers to the same region of memory.  This check is again encoded
-- symbolically in the final case, as we can't know if it is true or not during
-- simulation (without help from the SMT solver).
doPtrSub :: PtrOp sym w (LLVMPtr sym w)
doPtrSub = ptrOp $ \bak _mem w xPtr xBits yPtr yBits x y ->
  do let sym = backendGetSym bak
     both_bits <- andPred sym xBits yBits
     ptr_bits  <- andPred sym xPtr  yBits
     ptr_ptr   <- andPred sym xPtr  yPtr
     let nw = M.addrWidthNatRepr w

     cases bak (binOpLabel "ptr_sub" x y) muxLLVMPtr Nothing
       [ both_bits ~>
           endCase =<< llvmPointer_bv sym =<< bvSub sym (asBits x) (asBits y)

       , ptr_bits ~> endCase =<< ptrSub sym nw x (asBits y)

       , ptr_ptr ~>
           do sameAlloc <- natEq sym (ptrBase x) (ptrBase y)
              r  <- llvmPointer_bv sym =<< bvSub sym (asBits x) (asBits y)
              endCaseCheck sameAlloc "Pointers in different regions" r
       ]

-- | Truncation of a pointer down to a smaller size
--
-- We need to handle this as not a plain bitvector operation to enable us to
-- preserve the block id.  Some architectures do pointer operations (really, all
-- bitvector operations) at a higher bit width to observe overflow. Without this
-- special handling (to preserve the block id), it gets lost and corrupts
-- pointers.
--
-- We don't want to do any special checking: just truncate the offset and
-- preserve the block id.
doPtrTrunc
  :: ( IsSymInterface sym
     , 1 <= w'
     , (w' + 1) <= w
     )
  => CrucibleState s sym ext rtp blocks r ctx {- ^ Simulator state   -}
  -> GlobalVar Mem                            {- ^ Memory model      -}
  -> RegEntry sym (LLVMPointerType w)         {- ^ Argument 1        -}
  -> NatRepr w'                               {- ^ New width         -}
  -> IO (RegValue sym (LLVMPointerType w'), CrucibleState s sym ext rtp blocks r ctx)
doPtrTrunc st _memVar ptrEntry width = do
  let (Mem.LLVMPointer base offset) = regValue ptrEntry
  let sym = st ^. stateSymInterface
  ptr' <- Mem.LLVMPointer base <$> bvTrunc sym width offset
  return (ptr', st)

doPtrUExt
  :: ( IsSymInterface sym
     , 1 <= w
     , (w + 1) <= w'
     )
  => CrucibleState s sym ext rtp blocks r ctx {- ^ Simulator state   -}
  -> GlobalVar Mem                            {- ^ Memory model      -}
  -> RegEntry sym (LLVMPointerType w)         {- ^ Argument 1        -}
  -> NatRepr w'                               {- ^ New width         -}
  -> IO (RegValue sym (LLVMPointerType w'), CrucibleState s sym ext rtp blocks r ctx)
doPtrUExt st _memVar ptrEntry width = do
  let (Mem.LLVMPointer base offset) = regValue ptrEntry
  let sym = st ^. stateSymInterface
  ptr' <- Mem.LLVMPointer base <$> bvZext sym width offset
  return (ptr', st)


isAlignMask :: (IsSymInterface sym) => LLVMPtr sym w -> Maybe Integer
isAlignMask v =
  do 0 <- asNat (ptrBase v)
     let off = asBits v
         w   = fromInteger (intValue (bvWidth off))
     k <- BV.asUnsigned <$> asBV off
     let (zeros,ones) = break (testBit k) (take w [ 0 .. ])
     guard (all (testBit k) ones)
     return (fromIntegral (length zeros))

baseAlignment ::
  (1 <= w, IsSymInterface sym) =>
  LLVMPtr sym w ->
  MemImpl sym ->
  Maybe Alignment
baseAlignment ptr mem = do
  n <- asNat (ptrBase ptr)
  Mem.G.AllocInfo _ _ _ a _ <- Mem.G.possibleAllocInfo n (Mem.G.memAllocs (Mem.memImplHeap mem))
  return a

-- | Perform bitwise and on 'LLVMPtr' values
--
-- This is somewhat similar to 'doPtrAdd'.  This is a special case because many
-- machine code programs use bitwise masking to align pointers.  There are two
-- cases here:
--
-- * Both values are actually bitvectors (in which case we just delegate to the
--   low-level 'bvAndBits' operation)
-- * One of the values is an 'LLVMPtr' and the other is a literal that looks like a mask
--
-- If none of those cases is obviously true, this function generates assertions
-- that both values are actually bitvectors and uses the straightforward
-- operations (the last case in the Haskell-level case expression).
--
-- This operation is tricky for two reasons:
--
-- 1. The underlying 'LLVMPtr' type does not support a bitwise and operation
--    (since it makes less sense at the LLVM level, where alignment is specified
--    explicitly for each pointer and pointer operation)
-- 2. We do not know the alignment of the pointer being masked
--
-- If we knew the pointer alignment, we could simply generate an assertion that
-- the masking operation is safe and then mask the offset portion of the
-- pointer.  However, we do not have a guarantee of that, as pointer bases are
-- abstract in the LLVM memory model.
--
-- As a result, we do not know the exact effect of the masking operation on the
-- pointer.  Unfortunately, this means we have to treat the operation very
-- conservatively.  We determine how many bits the program is attempting to mask
-- off and create a symbolic constant of that size and subtract it from the
-- offset in the pointer.  This value represents the most that could possibly be
-- removed from the value (assuming the original pointer was actually properly
-- aligned); however, if the pointer was not actually sufficiently aligned, the
-- amount subtracted could be less.
--
-- This is not ideal, as there are not many constraints we can express about
-- this value being subtracted off.
doPtrAnd :: PtrOp sym w (LLVMPtr sym w)
doPtrAnd = ptrOp $ \bak mem w xPtr xBits yPtr yBits x y ->
  let sym = backendGetSym bak
      nw = M.addrWidthNatRepr w
      doPtrAlign amt isP isB v
        | amt == 0          = return v
        | amt == intValue nw = Mem.mkNullPointer sym nw
        | Just abv <- baseAlignment v mem
        , abv >= exponentToAlignment (fromIntegral amt) = do
        newoff <- bvAndBits sym (asBits x) (asBits y)
        return (Mem.LLVMPointer (ptrBase v) newoff)
        | Just 0 <- asNat (ptrBase v) = llvmPointer_bv sym =<<
                                        bvAndBits sym (asBits x) (asBits y)

        | otherwise =
        cases bak (binOpLabel "ptr_align" x y) muxLLVMPtr Nothing
          [ isB ~>
              endCase =<< llvmPointer_bv sym =<<
                                        bvAndBits sym (asBits x) (asBits y)
          , isP ~>
              do -- putStrLn ("ALIGNING TO " ++ show amt ++ " bits")
                 Just (Some n) <- return (someNat amt)
                 Just LeqProof <- return (testLeq (knownNat @1) n)
                 let nm = safeSymbol "align_amount"
                 least <- freshConstant sym nm (BaseBVRepr n)

                 Just LeqProof <- return (testLeq n nw)
                 let mostBits = subNat nw n
                 Just LeqProof <- return (testLeq (knownNat @1) mostBits)
                 most <- bvLit sym mostBits (BV.zero mostBits)

                 bts <- bvConcat sym most least

                 Refl <- return (minusPlusCancel nw n)

                 endCase =<< ptrSub sym nw v bts
                 -- We don't check for the validity of the pointer:
                 -- this is done upon use.
          ]
  in case (isAlignMask x, isAlignMask y) of
       (Just yes, _) -> doPtrAlign yes yPtr yBits y
       (_, Just yes) -> doPtrAlign yes xPtr xBits x
       _ -> do v1 <- doPtrToBits sym x
               v2 <- doPtrToBits sym y
               llvmPointer_bv sym =<< bvAndBits sym v1 v2

-- | Perform bitwise XOR on 'LLVMPtr' values
--
-- If both pointers are bitvectors, delegate to bvXorBits.
-- If one pointer is a bitvector and the other pointer has a constant base,
-- compare the number of bits needed to represent the bitvector with the
-- alignment of the pointer's base. If the base's alignment is sufficiently
-- large, perform bvXorBits on the offsets (keeping the base).
-- Otherwise, give up and convert non-bitvector pointers to fresh bitvectors.
doPtrXor :: PtrOp sym w (LLVMPtr sym w)
doPtrXor = ptrOp $ \bak mem _w xPtr xBits yPtr yBits x y -> do
  let sym = backendGetSym bak

  both_bits <- andPred sym xBits yBits
  ptr_bits  <- andPred sym xPtr  yBits
  bits_ptr  <- andPred sym xBits yPtr

  xToBits <- doPtrToBits sym x
  yToBits <- doPtrToBits sym y

  let ptrBaseAligned cond v u = case (baseAlignment v mem, requiredAlign u) of
        (Just abv, Just au)
          | abv >= au -> [cond ~> endCase =<< ptrXor sym v (asBits u)]
        _ -> []

  cases bak (binOpLabel "ptr_xor" x y) muxLLVMPtr Nothing $ mconcat
    [ [both_bits ~> endCase =<< llvmPointer_bv sym =<< bvXorBits sym (asBits x) (asBits y)]
    , ptrBaseAligned ptr_bits x y
    , ptrBaseAligned bits_ptr y x
    , [truePred sym ~> endCase =<< llvmPointer_bv sym =<< bvXorBits sym xToBits yToBits]
    ]
  where
    requiredAlign ptr = do
      let
        off = asBits ptr
        w = fromInteger (intValue (bvWidth off))
      k <- BV.asUnsigned <$> asBV off
      return $ exponentToAlignment $ fromIntegral $ length $ dropWhile (not . testBit k) [w, w-1 .. 0]
    ptrXor sym x yoff = do
      newoff <- bvXorBits sym (asBits x) yoff
      return (Mem.LLVMPointer (ptrBase x) newoff)


doPtrLt :: PtrOp sym w (RegValue sym BoolType)
doPtrLt = ptrOp $ \bak mem w xPtr xBits yPtr yBits x y ->
  do let sym = backendGetSym bak
     both_bits  <- andPred sym xBits yBits
     both_ptrs  <- andPred sym xPtr  yPtr
     sameRegion <- natEq sym (ptrBase x) (ptrBase y)
     okP1 <- isValidPtr sym mem w x
     okP2 <- isValidPtr sym mem w y
     ok <- andPred sym sameRegion =<< orPred sym both_bits
                      =<< andPred sym both_ptrs =<< andPred sym okP1 okP2
     undef <- mkUndefinedBool sym "ptr_lt"
     res <- bvUlt sym (asBits x) (asBits y)
     itePred sym ok res undef


doPtrLeq :: PtrOp sym w (RegValue sym BoolType)
doPtrLeq = ptrOp $ \bak mem w xPtr xBits yPtr yBits x y ->
  do let sym = backendGetSym bak
     both_bits  <- andPred sym xBits yBits
     both_ptrs  <- andPred sym xPtr  yPtr
     sameRegion <- natEq sym (ptrBase x) (ptrBase y)
     okP1 <- isValidPtr sym mem w x
     okP2 <- isValidPtr sym mem w y
     ok <- andPred sym sameRegion =<< orPred sym both_bits
                      =<< andPred sym both_ptrs =<< andPred sym okP1 okP2
     undef <- mkUndefinedBool sym "ptr_leq"
     res <- bvUle sym (asBits x) (asBits y)
     itePred sym ok res undef


doPtrEq :: PtrOp sym w (RegValue sym BoolType)
doPtrEq = ptrOp $ \bak _mem w xPtr xBits yPtr yBits x y ->
  do let sym = backendGetSym bak
     both_bits <- andPred sym xBits yBits
     both_ptrs <- andPred sym xPtr  yPtr
     xNull <- isNullPtr sym w x
     yNull <- isNullPtr sym w y
     both_null <- andPred sym xNull yNull
     undef <- mkUndefinedBool sym "ptr_eq"
     let nw = M.addrWidthNatRepr w
     cases bak (binOpLabel "ptr_eq" x y) itePred (Just undef)
       [ both_bits ~> endCase =<< bvEq sym (asBits x) (asBits y)
       , both_ptrs ~> endCase =<< ptrEq sym nw x y
       , both_null ~> endCase (truePred sym)
       , xNull ~> endCase (falsePred sym)
       , yNull ~> endCase (falsePred sym)
       ]

getEnd :: MemImpl sym -> M.Endianness
getEnd mem =
  case memEndian mem of
    BigEndian -> M.BigEndian
    LittleEndian -> M.LittleEndian

checkEndian :: M.Endianness -> M.Endianness -> Either String ()
checkEndian have need =
  when (need /= have) $ Left $
    unlines [ "[doReadMem] Endian mismatch:"
            , " *** Model: " ++ show have
            , " *** Read : " ++ show need
            ]

-- | Convert a mem repr to a memory model storage type.  May return an
-- error message if the mem repr is not supported.
memReprToStorageType :: M.Endianness -- ^ Expected endianness of arguments.
                     -> MemRepr ty
                     -> Either String Mem.StorageType
memReprToStorageType reqEnd memRep =
  case memRep of
    M.BVMemRepr bytes endian -> do
      checkEndian reqEnd endian
      pure $ Mem.bitvectorType (Bytes (intValue bytes))
    M.FloatMemRepr floatRep endian -> do
      checkEndian reqEnd endian
      case floatRep of
        M.SingleFloatRepr -> pure Mem.floatType
        M.DoubleFloatRepr -> pure Mem.doubleType
        M.X86_80FloatRepr -> pure Mem.x86_fp80Type
        _ -> Left $ "Do not support memory accesses to " ++ show floatRep ++ " values."
    M.PackedVecMemRepr n eltType -> do
      eltStorageType <- memReprToStorageType reqEnd eltType
      pure $ Mem.arrayType (natValue n) eltStorageType

-- | Convert a Crucible register value to a LLVM memory mode lvalue.
--
--     arg1 : What/how we are writing
--     arg2 : Previously computed storage type for value
--     arg3 : Value to write
resolveMemVal :: MemRepr ty ->
                 Mem.StorageType ->
                 RegValue sym (ToCrucibleType ty) ->
                 Mem.LLVMVal sym
resolveMemVal (M.BVMemRepr bytes _endian) _ (Mem.LLVMPointer base bits) =
  case leqMulPos (knownNat @8) bytes of
    LeqProof -> Mem.LLVMValInt base bits
resolveMemVal (M.FloatMemRepr floatRep _endian) _ val =
  case floatRep of
    M.SingleFloatRepr -> Mem.LLVMValFloat Mem.SingleSize   val
    M.DoubleFloatRepr -> Mem.LLVMValFloat Mem.DoubleSize   val
    M.X86_80FloatRepr -> Mem.LLVMValFloat Mem.X86_FP80Size val
    _ -> error $ "Do not support memory accesses to " ++ show floatRep ++ " values."
resolveMemVal (M.PackedVecMemRepr n eltType) stp val =
  case Mem.storageTypeF stp of
    Mem.Array cnt eltStp | cnt == natValue n, fromIntegral (V.length val) == natValue n ->
      Mem.LLVMValArray eltStp (resolveMemVal eltType eltStp <$> val)
    _ -> error $ "Unexpected storage type for packed vec."

-- | Report an unexpected value read from meory.
unexpectedMemVal :: Either String a
unexpectedMemVal = Left "Unexpected value read from memory."

-- | Translate from a memory value to a Crucible register value.
--
--     arg1 : Type of value to return
--     arg2 : Value to parse
memValToCrucible ::
  IsExpr (SymExpr sym) =>
  MemRepr ty ->
  Mem.LLVMVal sym ->
  Either String (RegValue sym (ToCrucibleType ty))
memValToCrucible memRep val =
  case memRep of
    -- Convert memory model value to pointer
    M.BVMemRepr bytes _endian ->
      do let bitw  = natMultiply (knownNat @8) bytes
         case val of
           Mem.LLVMValInt base off
             | Just Refl <- testEquality (bvWidth off) bitw ->
                 pure (Mem.LLVMPointer base off)
           _ -> unexpectedMemVal

    M.FloatMemRepr floatRep _endian ->
      case val of
        Mem.LLVMValFloat sz fltVal ->
          case (floatRep, sz) of
            (M.SingleFloatRepr, Mem.SingleSize) ->
              pure fltVal
            (M.DoubleFloatRepr, Mem.DoubleSize) ->
              pure fltVal
            (M.X86_80FloatRepr, Mem.X86_FP80Size) ->
              pure fltVal
            _ -> unexpectedMemVal
        _ -> unexpectedMemVal

    M.PackedVecMemRepr _expectedLen eltMemRepr -> do
      case val of
        Mem.LLVMValArray _ v -> do
          traverse (memValToCrucible eltMemRepr) v
        _ -> unexpectedMemVal

-- | Given a Boolean condition and two symbolic values associated with
-- a Macaw type, return a value denoting the first value if condition
-- is true and second value otherwise.
--
--     arg1 : Symbolic interface
--     arg2 : Description of memory layout of value
--     arg3 : Condition
--     arg4 : Value if condition is true
--     arg5 : Value if condition is false.
muxMemReprValue ::
  IsSymInterface sym =>
  sym ->
  MemRepr ty ->
  RegValue sym BoolType ->
  RegValue sym (ToCrucibleType ty) ->
  RegValue sym (ToCrucibleType ty) ->
  IO (RegValue sym (ToCrucibleType ty))
muxMemReprValue sym memRep cond x y =
  case memRep of
    M.BVMemRepr bytes _endian ->
      case leqMulPos (knownNat @8) bytes of
        LeqProof -> muxLLVMPtr sym cond x y
    M.FloatMemRepr _floatRep _endian ->
      baseTypeIte sym cond x y
    M.PackedVecMemRepr _ eltMemRepr -> do
      when (V.length x /= V.length y) $ do
        throwIO $ userError $ "Expected vectors to have same length"
      V.zipWithM (muxMemReprValue sym eltMemRepr cond) x y

-- | Use addr width to bring `HasPtrWidth` constraints in scope.
hasPtrClass :: M.AddrWidthRepr ptrW -> (Mem.HasPtrWidth ptrW => a) -> a
hasPtrClass ptrWidth v =
  let ?ptrWidth = M.addrWidthNatRepr ptrWidth
   in case ptrWidth of
        M.Addr32 -> v
        M.Addr64 -> v

doReadMem ::
  (IsSymBackend sym bak, Mem.HasLLVMAnn sym, ?memOpts :: Mem.MemOptions) =>
  bak ->
  MemImpl sym ->
  M.AddrWidthRepr ptrW ->
  MemRepr ty ->
  LLVMPtr sym ptrW ->
  IO (RegValue sym (ToCrucibleType ty))
doReadMem bak mem ptrWidth memRep ptr = hasPtrClass ptrWidth $
  do let sym = backendGetSym bak
     -- Check pointer is valid.
     -- Note. I think we should check that pointer has at least "bytes" bytes available?
     ok <- isValidPtr sym mem ptrWidth ptr
     check bak ok "doReadMem" $
       "Reading through an invalid pointer: " ++ show (Mem.ppPtr ptr)
     ty <- case memReprToStorageType (getEnd mem) memRep of
             Left msg -> throwIO $ userError msg
             Right tp -> pure tp

     let alignment = noAlignment -- default to byte alignment (FIXME)
     -- Load a value from the memory model type system.
     res <- Mem.assertSafe bak =<< Mem.loadRaw sym mem ptr ty alignment
     case memValToCrucible memRep res of
       Left err -> fail $ "[doReadMem] " ++ err
       Right crucVal -> return crucVal

-- | Conditional memory read
--
--     arg1 : Symbolic Interface
--     arg2 : Memory implementation
--     arg3 : Width of ptr
--     arg4 : What/how we are reading
--     arg5 : Condition
--     arg6 : Address to read
--     arg7 : Default answer if condition is false
doCondReadMem ::
  (IsSymBackend sym bak, Mem.HasLLVMAnn sym, ?memOpts :: Mem.MemOptions) =>
  bak ->
  MemImpl sym ->
  M.AddrWidthRepr ptrW ->
  MemRepr ty ->
  RegValue sym BoolType ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  IO (RegValue sym (ToCrucibleType ty))
doCondReadMem bak mem ptrWidth memRep cond ptr def = hasPtrClass ptrWidth $
  do let sym = backendGetSym bak
     -- Check pointer is valid.
     -- Note. I think we should check that pointer has at least "bytes" bytes available?
     ok  <- isValidPtr sym mem ptrWidth ptr
     check bak ok "doCondReadMem" $
       "Conditional read through an invalid pointer: " ++ show (Mem.ppPtr ptr)

     ty <- case memReprToStorageType (getEnd mem) memRep of
             Left msg -> throwIO $ userError msg
             Right tp -> pure tp

     let alignment = noAlignment -- default to byte alignment (FIXME)

     val <- Mem.assertSafe bak =<< Mem.loadRaw sym mem ptr ty alignment
     let useDefault msg =
           do notC <- notPred sym cond
              let errMsg = "[doCondReadMem] " ++ msg
              assert bak notC (AssertFailureSimError errMsg errMsg)
              return def
     case memValToCrucible memRep val of
       Left err -> useDefault err
       Right crucVal -> muxMemReprValue sym memRep cond crucVal def

-- | Write a Macaw value to memory.
--
--     arg1 : Symbolic Interface
--     arg2 : Heap prior to write
--     arg3 : Width of ptr
--     arg4 : What/how we are writing
--     arg5 : Address to write to
--     arg6 : Value to write
doWriteMem ::
  (IsSymBackend sym bak, Mem.HasLLVMAnn sym) =>
  bak ->
  MemImpl sym ->
  M.AddrWidthRepr ptrW ->
  MemRepr ty ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  IO (MemImpl sym)
doWriteMem bak mem ptrWidth memRep ptr val = hasPtrClass ptrWidth $
  do let sym = backendGetSym bak
     ok <- isValidPtr sym mem ptrWidth ptr
     check bak ok "doWriteMem" $
       "Write to an invalid location: " ++ show (Mem.ppPtr ptr)
     ty <- case memReprToStorageType (getEnd mem) memRep of
             Left msg -> throwIO $ userError msg
             Right tp -> pure tp
     let alignment = noAlignment -- default to byte alignment (FIXME)
     let memVal = resolveMemVal memRep ty val
     Mem.storeRaw bak mem ptr ty alignment memVal


-- | Write a Macaw value to memory if a condition holds.
--
--     arg1 : Symbolic Interface
--     arg2 : Heap prior to write
--     arg3 : Width of ptr
--     arg4 : What/how we are writing
--     arg5 : Condition that must hold if we write.
--     arg6 : Address to write to
--     arg7 : Value to write
doCondWriteMem ::
  (IsSymBackend sym bak, Mem.HasLLVMAnn sym) =>
  bak ->
  MemImpl sym ->
  M.AddrWidthRepr ptrW ->
  MemRepr ty ->
  Pred sym ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  IO (MemImpl sym)
doCondWriteMem bak mem ptrWidth memRep cond ptr val = hasPtrClass ptrWidth $
  do let sym = backendGetSym bak
     ok <- isValidPtr sym mem ptrWidth ptr
     condOk <- impliesPred sym cond ok
     check bak condOk "doWriteMem" $
       "Write to an invalid location: " ++ show (Mem.ppPtr ptr)
     ty <- case memReprToStorageType (getEnd mem) memRep of
             Left msg -> throwIO $ userError msg
             Right tp -> pure tp
     let alignment = noAlignment -- default to byte alignment (FIXME)
     let memVal = resolveMemVal memRep ty val
     Mem.condStoreRaw bak mem cond ptr ty alignment memVal
