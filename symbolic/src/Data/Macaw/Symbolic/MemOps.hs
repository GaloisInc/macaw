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
  , GlobalMap
  , doPtrAdd
  , doPtrSub
  , doPtrMux
  , doPtrEq
  , doPtrLt
  , doPtrLeq
  , doPtrAnd
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
          ( CrucibleState
          , stateSymInterface
          , stateTree
          , actFrame
          , gpGlobals
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

import           Lang.Crucible.LLVM.DataLayout (EndianForm(..), noAlignment)
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

-- | The base part of a point.
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
type GlobalMap sym mem w
  = sym                        {-^ The symbolic backend -} ->
    GetIntrinsic sym mem       {-^ The global handle to the memory model -} ->
    RegValue sym NatType       {-^ The region index of the pointer being translated -} ->
    RegValue sym (BVType w)    {-^ The offset of the pointer into the region -} ->
    IO (LLVMPtr sym w)

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
  IsSymInterface sym =>
  sym ->
  RegValue sym Mem ->
  GlobalMap sym Mem w ->
  LLVMPtr sym w ->
  IO (LLVMPtr sym w)
tryGlobPtr sym mem mapBVAddress val
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
      mapBVAddress sym mem (ptrBase val) (asBits val)

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
ptrOp ::
  ( (1 <= w) =>
    sym ->
    RegValue sym Mem ->
    M.AddrWidthRepr w ->
    Pred sym -> Pred sym -> Pred sym -> Pred sym ->
    LLVMPtr sym w -> LLVMPtr sym w -> IO a
  ) ->
  PtrOp sym w a
ptrOp k st mvar w x0 y0 =
  do mem <- getMem st mvar
     LeqProof <- return (addrWidthIsPos w)
     let sym = st^.stateSymInterface
         x   = regValue x0
         y   = regValue y0

     zero <- natLit sym 0

     xBits <- natEq sym (ptrBase x) zero
     xPtr <- notPred sym xBits

     yBits <- natEq sym (ptrBase y) zero
     yPtr <- notPred sym yBits

     a <- k sym mem w xPtr xBits yPtr yBits x y
     return (a,st)

mkName :: String -> IO SolverSymbol
mkName x = case userSymbol x of
             Right v -> return v
             Left err ->
               fail $ unlines
                        [ "[bug] " ++ show x ++ " is not a valid identifier?"
                        , "*** " ++ show err
                        ]

mkUndefined ::
  (IsSymInterface sym) =>
  sym -> String -> BaseTypeRepr t -> IO (RegValue sym (BaseToType t))
mkUndefined sym unm ty =
  do let name = "undefined_" ++ unm
     nm <- mkName name
     freshConstant sym nm ty

-- | A fresh bit-vector variable
mkUndefinedBV ::
  (IsSymInterface sym, 1 <= w) =>
  sym -> String -> NatRepr w -> IO (RegValue sym (BVType w))
mkUndefinedBV sym nm w =
  mkUndefined sym (nm ++ "bv" ++ show w ++ "_") (BaseBVRepr w)

-- | A fresh boolean variable
mkUndefinedBool ::
  (IsSymInterface sym) => sym -> String -> IO (RegValue sym BoolType)
mkUndefinedBool sym nm =
  mkUndefined sym (nm ++ "bool_") BaseBoolRepr

mkUndefinedPtr :: (IsSymInterface sym, 1 <= w) =>
  sym -> String -> NatRepr w -> IO (LLVMPtr sym w)
mkUndefinedPtr sym nm w =
  do base <- mkUndefined sym ("ptr_base_" ++ nm) BaseNatRepr
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
data LookupFunctionHandle sym arch = LookupFunctionHandle
     (forall rtp blocks r ctx
   . CrucibleState (MacawSimulatorState sym) sym (MacawExt arch) rtp blocks r ctx
  -> MemImpl sym
  -> Ctx.Assignment (C.RegValue' sym) (MacawCrucibleRegTypes arch)
  -> IO (C.FnHandle (Ctx.EmptyCtx Ctx.::> ArchRegStruct arch) (ArchRegStruct arch), CrucibleState (MacawSimulatorState sym) sym (MacawExt arch) rtp blocks r ctx))

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
doGetGlobal st mvar globs addr = do
  let sym = st^.stateSymInterface
  mem <- getMem st mvar
  regionNum <- natLit sym (fromIntegral (M.addrBase addr))
  let w = M.addrWidthNatRepr (M.addrWidthRepr addr)
  offset <- bvLit sym w (BV.mkBV w (M.memWordToUnsigned (M.addrOffset addr)))
  ptr <- globs sym mem regionNum offset
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

check :: IsSymInterface sym => sym -> Pred sym -> String -> String -> IO ()
check sym valid name msg = assert sym valid
                    $ AssertFailureSimError errMsg errMsg
  where
    errMsg = "[" ++ name ++ "] " ++ msg

-- | Define an operation by cases.
cases ::
  (IsSymInterface sym) =>
  sym         {- ^ Simulator -} ->
  String      {- ^ Name of operation (for assertions) -} ->
  (sym -> Pred sym -> a -> a -> IO a) {- Mux results -} ->
  Maybe a           {- ^ Default: use this if none of the cases matched -} ->

  [(Pred sym,  IO ([(Pred sym,String)], a))]
    {- ^ Cases: (predicate when valid, result + additional checks) -} ->
  IO a
cases sym name mux def opts =
  case def of
    Just _ -> combine =<< mapM doCase opts
    Nothing ->
      do ok <- oneOf (map fst opts)
         check sym ok name ("Invalid arguments for " ++ show name)
         combine =<< mapM doCase opts
  where
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
       check sym valid name msg

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

doPtrMux :: Pred sym -> PtrOp sym w (LLVMPtr sym w)
doPtrMux c = ptrOp $ \sym _ w xPtr xBits yPtr yBits x y ->
  do both_bits <- andPred sym xBits yBits
     both_ptrs <- andPred sym xPtr  yPtr
     undef     <- mkUndefinedPtr sym "ptr_mux" (M.addrWidthNatRepr w)
     cases sym (binOpLabel "ptr_mux" x y) muxLLVMPtr (Just undef)
       [ both_bits ~>
           endCase =<< llvmPointer_bv sym =<< bvIte sym c (asBits x) (asBits y)
       , both_ptrs ~>
           endCase =<< muxLLVMPtr sym c x y
       ]

doPtrAdd :: PtrOp sym w (LLVMPtr sym w)
doPtrAdd = ptrOp $ \sym _ w xPtr xBits yPtr yBits x y ->
  do both_bits <- andPred sym xBits yBits
     ptr_bits  <- andPred sym xPtr  yBits
     bits_ptr  <- andPred sym xBits yPtr
     let nw = M.addrWidthNatRepr w
     a <- cases sym (binOpLabel "ptr_add" x y) muxLLVMPtr Nothing
       [ both_bits ~>
           endCase =<< llvmPointer_bv sym =<< bvAdd sym (asBits x) (asBits y)

       , ptr_bits ~> endCase =<< ptrAdd sym nw x (asBits y)
       , bits_ptr ~> endCase =<< ptrAdd sym nw y (asBits x)
       ]
     return a

doPtrSub :: PtrOp sym w (LLVMPtr sym w)
doPtrSub = ptrOp $ \sym mem w xPtr xBits yPtr yBits x y ->
  do both_bits <- andPred sym xBits yBits
     ptr_bits  <- andPred sym xPtr  yBits
     ptr_ptr   <- andPred sym xPtr  yPtr
     let nw = M.addrWidthNatRepr w

     cases sym (binOpLabel "ptr_sub" x y) muxLLVMPtr Nothing
       [ both_bits ~>
           endCase =<< llvmPointer_bv sym =<< bvSub sym (asBits x) (asBits y)

       , ptr_bits ~> endCase =<< ptrSub sym nw x (asBits y)

       , ptr_ptr ~>
           do okP1 <- isValidPtr sym mem w x
              okP2 <- isValidPtr sym mem w y
              sameAlloc <- natEq sym (ptrBase x) (ptrBase y)
              ok <- andPred sym sameAlloc =<< andPred sym okP1 okP2
              r  <- llvmPointer_bv sym =<< bvSub sym (asBits x) (asBits y)
              endCaseCheck ok "Pointers in different regions" r
       ]

isAlignMask :: (IsSymInterface sym) => LLVMPtr sym w -> Maybe Integer
isAlignMask v =
  do 0 <- asNat (ptrBase v)
     let off = asBits v
         w   = fromInteger (intValue (bvWidth off))
     k <- BV.asUnsigned <$> asBV off
     let (zeros,ones) = break (testBit k) (take w [ 0 .. ])
     guard (all (testBit k) ones)
     return (fromIntegral (length zeros))

doPtrAnd :: PtrOp sym w (LLVMPtr sym w)
doPtrAnd = ptrOp $ \sym _mem w xPtr xBits yPtr yBits x y ->
  let nw = M.addrWidthNatRepr w
      doPtrAlign amt isP isB v
        | amt == 0          = return v
        | amt == intValue nw = Mem.mkNullPointer sym nw
        | Just 0 <- asNat (ptrBase v) = llvmPointer_bv sym =<<
                                        bvAndBits sym (asBits x) (asBits y)

        | otherwise =
        cases sym (binOpLabel "ptr_align" x y) muxLLVMPtr Nothing
          [ isB ~>
              endCase =<< llvmPointer_bv sym =<<
                                        bvAndBits sym (asBits x) (asBits y)
          , isP ~>
              do -- putStrLn ("ALIGNING TO " ++ show amt ++ " bits")
                 Just (Some n) <- return (someNat amt)
                 Just LeqProof <- return (testLeq (knownNat @1) n)
                 nm <- mkName "align_amount"
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



doPtrLt :: PtrOp sym w (RegValue sym BoolType)
doPtrLt = ptrOp $ \sym mem w xPtr xBits yPtr yBits x y ->
  do both_bits  <- andPred sym xBits yBits
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
doPtrLeq = ptrOp $ \sym mem w xPtr xBits yPtr yBits x y ->
  do both_bits  <- andPred sym xBits yBits
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
doPtrEq = ptrOp $ \sym mem w xPtr xBits yPtr yBits x y ->
  do both_bits <- andPred sym xBits yBits
     both_ptrs <- andPred sym xPtr  yPtr
     undef <- mkUndefinedBool sym "ptr_eq"
     let nw = M.addrWidthNatRepr w
     cases sym (binOpLabel "ptr_eq" x y) itePred (Just undef)
       [ both_bits ~> endCase =<< bvEq sym (asBits x) (asBits y)
       , both_ptrs ~>
            do okP1 <- isValidPtr sym mem w x
               okP2 <- isValidPtr sym mem w y
               ok <- andPred sym okP1 okP2
               ps <- ptrEq sym nw x y
               endCaseCheck ok "Comparing invalid pointers" ps
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
      pure $ Mem.arrayType (Bytes (intValue n)) eltStorageType

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
    Mem.Array cnt eltStp | cnt == Bytes (intValue n), fromIntegral (V.length val) == natValue n ->
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
  (IsSymInterface sym, Mem.HasLLVMAnn sym) =>
  sym ->
  MemImpl sym ->
  M.AddrWidthRepr ptrW ->
  MemRepr ty ->
  LLVMPtr sym ptrW ->
  IO (RegValue sym (ToCrucibleType ty))
doReadMem sym mem ptrWidth memRep ptr = hasPtrClass ptrWidth $
  do -- Check pointer is valid.
     -- Note. I think we should check that pointer has at least "bytes" bytes available?
     ok <- isValidPtr sym mem ptrWidth ptr
     check sym ok "doReadMem" $
       "Reading through an invalid pointer: " ++ show (Mem.ppPtr ptr)
     ty <- case memReprToStorageType (getEnd mem) memRep of
             Left msg -> throwIO $ userError msg
             Right tp -> pure tp

     let alignment = noAlignment -- default to byte alignment (FIXME)
     -- Load a value from the memory model type system.
     fm <- getFloatMode sym
     res <- Mem.assertSafe sym =<< Mem.loadRaw sym fm mem ptr ty alignment
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
  (IsSymInterface sym, Mem.HasLLVMAnn sym) =>
  sym ->
  MemImpl sym ->
  M.AddrWidthRepr ptrW ->
  MemRepr ty ->
  RegValue sym BoolType ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  IO (RegValue sym (ToCrucibleType ty))
doCondReadMem sym mem ptrWidth memRep cond ptr def = hasPtrClass ptrWidth $
  do -- Check pointer is valid.
     -- Note. I think we should check that pointer has at least "bytes" bytes available?
     ok  <- isValidPtr sym mem ptrWidth ptr
     check sym ok "doCondReadMem" $
       "Conditional read through an invalid pointer: " ++ show (Mem.ppPtr ptr)

     ty <- case memReprToStorageType (getEnd mem) memRep of
             Left msg -> throwIO $ userError msg
             Right tp -> pure tp

     let alignment = noAlignment -- default to byte alignment (FIXME)

     fm <- getFloatMode sym
     val <- Mem.assertSafe sym =<< Mem.loadRaw sym fm mem ptr ty alignment
     let useDefault msg =
           do notC <- notPred sym cond
              let errMsg = "[doCondReadMem] " ++ msg
              assert sym notC (AssertFailureSimError errMsg errMsg)
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
  (IsSymInterface sym, Mem.HasLLVMAnn sym) =>
  sym ->
  MemImpl sym ->
  M.AddrWidthRepr ptrW ->
  MemRepr ty ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  IO (MemImpl sym)
doWriteMem sym mem ptrWidth memRep ptr val = hasPtrClass ptrWidth $
  do ok <- isValidPtr sym mem ptrWidth ptr
     check sym ok "doWriteMem" $
       "Write to an invalid location: " ++ show (Mem.ppPtr ptr)
     ty <- case memReprToStorageType (getEnd mem) memRep of
             Left msg -> throwIO $ userError msg
             Right tp -> pure tp
     let alignment = noAlignment -- default to byte alignment (FIXME)
     let memVal = resolveMemVal memRep ty val
     fm <- getFloatMode sym
     Mem.storeRaw sym fm mem ptr ty alignment memVal


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
  (IsSymInterface sym, Mem.HasLLVMAnn sym) =>
  sym ->
  MemImpl sym ->
  M.AddrWidthRepr ptrW ->
  MemRepr ty ->
  Pred sym ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  IO (MemImpl sym)
doCondWriteMem sym mem ptrWidth memRep cond ptr val = hasPtrClass ptrWidth $
  do ok <- isValidPtr sym mem ptrWidth ptr
     condOk <- impliesPred sym cond ok
     check sym condOk "doWriteMem" $
       "Write to an invalid location: " ++ show (Mem.ppPtr ptr)
     ty <- case memReprToStorageType (getEnd mem) memRep of
             Left msg -> throwIO $ userError msg
             Right tp -> pure tp
     let alignment = noAlignment -- default to byte alignment (FIXME)
     let memVal = resolveMemVal memRep ty val
     Mem.condStoreRaw sym mem cond ptr ty alignment memVal
