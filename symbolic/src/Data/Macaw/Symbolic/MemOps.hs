-- This module deals with the fact that a number of operations work differently,
-- depending on if they are applied to pointers or bit-vectors.
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language ImplicitParams #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language TypeApplications #-}
module Data.Macaw.Symbolic.MemOps
  ( PtrOp
  , doPtrAdd
  , doPtrSub
  , doPtrMux
  , doPtrEq
  , doPtrLt
  , doPtrLeq
  , doReadMem
  ) where

import Control.Lens((^.))

import Lang.Crucible.Simulator.ExecutionTree
          ( CrucibleState
          , stateSymInterface
          , stateTree
          , actFrame
          , gpGlobals
          )
import Lang.Crucible.Simulator.RegMap(RegEntry,regValue)
import Lang.Crucible.Simulator.RegValue(RegValue)
import Lang.Crucible.Simulator.GlobalState(lookupGlobal)
import Lang.Crucible.Simulator.SimError(SimErrorReason(AssertFailureSimError))
import Lang.Crucible.CFG.Common(GlobalVar)
import Lang.Crucible.Types
import Lang.Crucible.Solver.Interface

import Lang.Crucible.LLVM.MemModel
          ( Mem, LLVMPointerType, LLVMPtr, isValidPointer, memEndian
          , coerceAny
          , doLoad)
import Lang.Crucible.LLVM.MemModel.Pointer
          ( llvmPointerView, muxLLVMPtr, llvmPointer_bv, ptrAdd, ptrSub, ptrEq
          , pattern LLVMPointerRepr
          )
import Lang.Crucible.LLVM.MemModel.Type(bitvectorType)
import Lang.Crucible.LLVM.DataLayout(toAlignment,EndianForm(..))
import Lang.Crucible.LLVM.Bytes(toBytes)

import Data.Macaw.Symbolic.CrucGen(lemma1_16)
import Data.Macaw.Symbolic.PersistentState(ToCrucibleType)
import Data.Macaw.CFG.Core(MemRepr(BVMemRepr))
import qualified Data.Macaw.Memory as M (Endianness(..))

-- | This is the form of binary operation needed by the simulator.
-- Note that even though the type suggests that we might modify the
-- state, we don't actually do it.
type PtrOp sym w a =
  forall s ext rtp blocks r ctx.
  (IsSymInterface sym, 16 <= w)                                      =>
  CrucibleState s sym ext rtp blocks r ctx {- ^ Simulator state   -} ->
  GlobalVar Mem                            {- ^ Memory model      -} ->
  NatRepr w                                {- ^ Width of pointer  -} ->
  RegEntry sym (LLVMPointerType w)         {- ^ Argument 1        -} ->
  RegEntry sym (LLVMPointerType w)         {- ^ Argument 2        -} ->
  IO (a, CrucibleState s sym ext rtp blocks r ctx)


doPtrMux :: Pred sym -> PtrOp sym w (LLVMPtr sym w)
doPtrMux c = ptrOp $ \sym _ _ xPtr xBits yPtr yBits x y ->
  do both_bits <- andPred sym xBits yBits
     both_ptrs <- andPred sym xPtr  yPtr
     cases sym "ptr_mux" muxLLVMPtr
       [ both_bits ~>
           endCase =<< llvmPointer_bv sym =<< bvIte sym c (asBits x) (asBits y)
       , both_ptrs ~>
           endCase =<< muxLLVMPtr sym c x y
       ]

doPtrAdd :: PtrOp sym w (LLVMPtr sym w)
doPtrAdd = ptrOp $ \sym mem w xPtr xBits yPtr yBits x y ->
  do both_bits <- andPred sym xBits yBits
     ptr_bits  <- andPred sym xPtr  yBits
     bits_ptr  <- andPred sym xBits yPtr

     cases sym "ptr_add" muxLLVMPtr
       [ both_bits ~>
           endCase =<< llvmPointer_bv sym =<< bvAdd sym (asBits x) (asBits y)

       , ptr_bits ~>
           do r  <- ptrAdd sym w x (asBits y)
              ok <- let ?ptrWidth = w in isValidPointer sym r mem
              endCaseCheck ok "Invalid result" r

       , bits_ptr ~>
           do  r <- ptrAdd sym w y (asBits x)
               ok <- let ?ptrWidth = w in isValidPointer sym r mem
               endCaseCheck ok "Invalid result" r
       ]


doPtrSub :: PtrOp sym w (LLVMPtr sym w)
doPtrSub = ptrOp $ \sym mem w xPtr xBits yPtr yBits x y ->
  do both_bits <- andPred sym xBits yBits
     ptr_bits  <- andPred sym xPtr  yBits
     ptr_ptr   <- andPred sym xPtr  yPtr

     cases sym "ptr_sub" muxLLVMPtr
       [ both_bits ~>
           endCase =<< llvmPointer_bv sym =<< bvSub sym (asBits x) (asBits y)

       , ptr_bits ~>
           do r <- ptrSub sym w x (asBits y)
              ok <- let?ptrWidth = w in isValidPointer sym r mem
              endCaseCheck ok "Invalid result" r

       , ptr_ptr ~>
           do r  <- llvmPointer_bv sym =<< bvSub sym (asBits x) (asBits y)
              ok <- natEq sym (ptrBase x) (ptrBase y)
              endCaseCheck ok "Pointers in different regions" r
       ]


doPtrLt :: PtrOp sym w (RegValue sym BoolType)
doPtrLt = ptrOp $ \sym _ _ xPtr xBits yPtr yBits x y ->
  do both_bits  <- andPred sym xBits yBits
     both_ptrs  <- andPred sym xPtr  yPtr
     sameRegion <- natEq sym (ptrBase x) (ptrBase y)
     ok <- andPred sym sameRegion =<< orPred sym both_bits both_ptrs
     addAssertion sym ok (AssertFailureSimError "[ptr_lt] Invalid arguments")
     bvUlt sym (asBits x) (asBits y)


doPtrLeq :: PtrOp sym w (RegValue sym BoolType)
doPtrLeq = ptrOp $ \sym _ _ xPtr xBits yPtr yBits x y ->
  do both_bits  <- andPred sym xBits yBits
     both_ptrs  <- andPred sym xPtr  yPtr
     sameRegion <- natEq sym (ptrBase x) (ptrBase y)
     ok <- andPred sym sameRegion =<< orPred sym both_bits both_ptrs
     addAssertion sym ok (AssertFailureSimError "[ptr_leq] Invalid arguments")
     bvUle sym (asBits x) (asBits y)


doPtrEq :: PtrOp sym w (RegValue sym BoolType)
doPtrEq = ptrOp $ \sym _ w xPtr xBits yPtr yBits x y ->
  do both_bits <- andPred sym xBits yBits
     both_ptrs <- andPred sym xPtr  yPtr
     cases sym "ptr_eq" itePred
       [ both_bits ~> endCase =<< bvEq sym (asBits x) (asBits y)
       , both_ptrs ~> endCase =<< ptrEq sym w x y
       ]

doReadMem ::
  (IsSymInterface sym, 16 <= ptrW) =>
  CrucibleState s sym ext rtp blocks r ctx {- ^ Simulator state   -} ->
  GlobalVar Mem ->
  NatRepr ptrW ->
  MemRepr ty ->
  RegEntry sym (LLVMPointerType ptrW) ->
  IO ( RegValue sym (ToCrucibleType ty)
     , CrucibleState s sym ext rtp blocks r ctx
     )
doReadMem st mvar w (BVMemRepr bytes endian) ptr =
  do mem <- getMem st mvar
     case (endian, memEndian mem) of
       (M.BigEndian, BigEndian) -> return ()
       (M.LittleEndian, LittleEndian) -> return ()
       (need,have) -> fail $ unlines [ "[doReadMem] Endian mismatch:"
                                     , " *** Model: " ++ show have
                                     , " *** Read : " ++ show need ]

     let sym        = stateSymInterface st
         ty         = bitvectorType (toBytes (widthVal bytes))

         {- XXX: The alginment requirements should be part of the spec.
         For example, on X86, there are aligned reads and unlaigned reads,
         which makes different assumptions about the alignment of the data -}
         Just align = toAlignment (toBytes (1::Int))

     LeqProof <- return (lemma1_16 w)
     LeqProof <- return (leqMulPos (knownNat @8) bytes)

     anyval <- let ?ptrWidth = w in doLoad sym mem (regValue ptr) ty align
     let repr = LLVMPointerRepr (natMultiply (knownNat @8) bytes)
     a <- coerceAny sym repr anyval
     return (a,st)


--------------------------------------------------------------------------------
-- Utilities

infix 0 ~>

(~>) :: a -> b -> (a,b)
x ~> y = (x,y)

endCase :: Monad m => a -> m ([b],a)
endCase r = return ([],r)

endCaseCheck :: Monad m => a -> b -> c -> m ([(a,b)],c)
endCaseCheck a b c = return ([(a,b)],c)

-- | The offset part of a pointer.
asBits :: LLVMPtr sym w -> RegValue sym (BVType w)
asBits = snd . llvmPointerView

-- | The base part of a point.
ptrBase :: LLVMPtr sym w -> RegValue sym NatType
ptrBase = fst . llvmPointerView

-- | Is this value a bit-vector (i.e., not a pointer).
-- Note that the NULL pointer is actually also a bit-vector.
isBitVec :: IsSymInterface sym => sym -> LLVMPtr sym w -> IO (Pred sym)
isBitVec sym p = natEq sym (ptrBase p) =<< natLit sym 0

-- | Classify the arguments, and continue.
ptrOp ::
  ( (1 <= w) =>
    sym ->
    RegValue sym Mem ->
    NatRepr w ->
    Pred sym -> Pred sym -> Pred sym -> Pred sym ->
    LLVMPtr sym w -> LLVMPtr sym w -> IO a
  ) ->
  PtrOp sym w a
ptrOp k st mvar w x0 y0 =
  do mem <- getMem st mvar
     LeqProof <- return (lemma1_16 w)
     let sym = stateSymInterface st
         x   = regValue x0
         y   = regValue y0
     xPtr     <- let ?ptrWidth = w in isValidPointer sym x mem
     yPtr     <- let ?ptrWidth = w in isValidPointer sym y mem
     xBits    <- isBitVec sym x
     yBits    <- isBitVec sym x
     a <- k sym mem w xPtr xBits yPtr yBits x y
     return (a,st)

-- | Get the current model of the memory.
getMem :: CrucibleState s sym ext rtp blocks r ctx ->
          GlobalVar Mem ->
          IO (RegValue sym Mem)
getMem st mvar =
  case lookupGlobal mvar (st ^. stateTree . actFrame . gpGlobals) of
    Just mem -> return mem
    Nothing  -> fail ("Global heap value not initialized: " ++ show mvar)

-- | Define an operation by cases.
cases ::
  (IsSymInterface sym) =>
  sym         {- ^ Simulator -} ->
  String      {- ^ Name of operation (for assertions) -} ->
  (sym -> Pred sym -> a -> a -> IO a) {- Mux results -} ->

  -- | Cases: (name, predicate when valid, result + additional checks)
  [(Pred sym,  IO ([(Pred sym,String)], a))] ->
  IO a
cases sym name mux opts =
  do ok <- oneOf (map fst opts)
     check ok "Invalid arguments"
     combine =<< mapM doCase opts
  where
  oneOf []       = return (falsePred sym)   -- shouldn't happen
  oneOf [a]      = return a
  oneOf (a : xs) = orPred sym a =<< oneOf xs

  combine [] = fail "[bug] Empty cases"
  combine [(_,a)] = return a
  combine ((p,a) : more) = mux sym p a =<< combine more

  check ok msg =
    addAssertion sym ok (AssertFailureSimError ("[" ++ name ++ "] " ++ msg))

  doCase (p,m) =
    do (checks,a) <- m
       mapM_ (subCheck p) checks
       return (p,a)

  subCheck cp (p,msg) =
    do valid <- impliesPred sym cp p
       check valid msg


