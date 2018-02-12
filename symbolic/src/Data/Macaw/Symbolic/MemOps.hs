-- This module deals with the fact that a number of operations work differently,
-- depending on if they are applied to pointers or bit-vectors.
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language ImplicitParams #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language TypeApplications #-}
{-# Language PatternGuards #-}
module Data.Macaw.Symbolic.MemOps
  ( PtrOp
  , doPtrAdd
  , doPtrSub
  , doPtrMux
  , doPtrEq
  , doPtrLt
  , doPtrLeq
  , doReadMem
  , doCondReadMem
  , doWriteMem
  ) where

import Control.Lens((^.),(&),(%~))

import Lang.Crucible.Simulator.ExecutionTree
          ( CrucibleState
          , stateSymInterface
          , stateTree
          , actFrame
          , gpGlobals
          )
import Lang.Crucible.Simulator.RegMap(RegEntry,regValue)
import Lang.Crucible.Simulator.RegValue(RegValue)
import Lang.Crucible.Simulator.GlobalState(lookupGlobal,insertGlobal)
import Lang.Crucible.Simulator.SimError(SimErrorReason(AssertFailureSimError))
import Lang.Crucible.CFG.Common(GlobalVar)
import Lang.Crucible.Types
import Lang.Crucible.Solver.Interface

import Lang.Crucible.LLVM.MemModel
          ( Mem, MemImpl, LLVMPointerType, LLVMPtr, isValidPointer, memEndian
          , LLVMVal(LLVMValInt)
          , loadRaw
          , loadRawWithCondition
          , storeRaw
          )
import Lang.Crucible.LLVM.MemModel.Pointer
          ( llvmPointerView, muxLLVMPtr, llvmPointer_bv, ptrAdd, ptrSub, ptrEq
          , pattern LLVMPointer
          )
import Lang.Crucible.LLVM.MemModel.Type(bitvectorType)
import Lang.Crucible.LLVM.DataLayout(EndianForm(..))
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
     checkEndian mem endian

     let sym   = stateSymInterface st
         ty    = bitvectorType (toBytes (widthVal bytes))
         bitw  = natMultiply (knownNat @8) bytes

     LeqProof <- return (lemma1_16 w)
     LeqProof <- return (leqMulPos (knownNat @8) bytes)

     val <- let ?ptrWidth = w in loadRaw sym mem (regValue ptr) ty
     a   <- case valToBits bitw val of
              Just a  -> return a
              Nothing -> fail "[doReadMem] We read an unexpected value"

     return (a,st)



doCondReadMem ::
  (IsSymInterface sym, 16 <= ptrW) =>
  CrucibleState s sym ext rtp blocks r ctx {- ^ Simulator state   -} ->
  GlobalVar Mem ->                         {- ^ Memory model -}
  NatRepr ptrW                             {- ^ Width of ptr -} ->
  MemRepr ty                               {- ^ What/how we are reading -} ->
  RegEntry sym BoolType                    {- ^ Condition -} ->
  RegEntry sym (LLVMPointerType ptrW)      {- ^ Pointer -} ->
  RegEntry sym (ToCrucibleType ty)         {- ^ Default answer -} ->
  IO ( RegValue sym (ToCrucibleType ty)
     , CrucibleState s sym ext rtp blocks r ctx
     )
doCondReadMem st mvar w (BVMemRepr bytes endian) cond0 ptr def0 =
  do let cond = regValue cond0
         def  = regValue def0
     mem <- getMem st mvar
     checkEndian mem endian
     let sym   = stateSymInterface st
         ty    = bitvectorType (toBytes (widthVal bytes))
         bitw  = natMultiply (knownNat @8) bytes

     LeqProof <- return (lemma1_16 w)
     LeqProof <- return (leqMulPos (knownNat @8) bytes)

     val <- let ?ptrWidth = w in loadRawWithCondition sym mem (regValue ptr) ty

     let useDefault msg =
           do notC <- notPred sym cond
              addAssertion sym notC
                 (AssertFailureSimError ("[doCondReadMem] " ++ msg))
              return def

     a <- case val of
            Right (p,r,v) | Just a <- valToBits bitw v ->
              do grd <- impliesPred sym cond p
                 addAssertion sym grd r
                 muxLLVMPtr sym cond a def
            Right _ -> useDefault "Unexpected value read from memory."
            Left err -> useDefault err

     return (a,st)


doWriteMem ::
  (IsSymInterface sym, 16 <= ptrW) =>
  CrucibleState s sym ext rtp blocks r ctx {- ^ Simulator state   -} ->
  GlobalVar Mem ->                         {- ^ Memory model -}
  NatRepr ptrW                             {- ^ Width of ptr -} ->
  MemRepr ty                               {- ^ What/how we are writing -} ->
  RegEntry sym (LLVMPointerType ptrW)      {- ^ Pointer -} ->
  RegEntry sym (ToCrucibleType ty)         {- ^ Write this value -} ->
  IO ( RegValue sym UnitType
     , CrucibleState s sym ext rtp blocks r ctx
     )
doWriteMem st mvar w (BVMemRepr bytes endian) ptr val =
  do mem <- getMem st mvar
     checkEndian mem endian

     let sym   = stateSymInterface st
         ty    = bitvectorType (toBytes (widthVal bytes))

     LeqProof <- return (lemma1_16 w)
     LeqProof <- return (leqMulPos (knownNat @8) bytes)

     let ?ptrWidth = w
     let v0 = regValue val
         v  = LLVMValInt (ptrBase v0) (asBits v0)
     mem1 <- storeRaw sym mem (regValue ptr) ty v
     return ((), setMem st mvar mem1)





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

setMem :: CrucibleState s sym ext rtp blocks r ctx ->
          GlobalVar Mem ->
          MemImpl sym ->
          CrucibleState s sym ext rtp blocks r ctx
setMem st mvar mem =
  st & stateTree . actFrame . gpGlobals %~ insertGlobal mvar mem


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


valToBits :: (IsSymInterface sym, 1 <= w) =>
  NatRepr w -> LLVMVal sym -> Maybe (LLVMPtr sym w)
valToBits w val =
  case val of
    LLVMValInt base off | Just Refl <- testEquality (bvWidth off) w ->
                                        return (LLVMPointer base off)
    _ -> Nothing

checkEndian :: MemImpl sym -> M.Endianness -> IO ()
checkEndian mem endian =
  case (endian, memEndian mem) of
    (M.BigEndian, BigEndian) -> return ()
    (M.LittleEndian, LittleEndian) -> return ()
    (need,have) -> fail $ unlines [ "[doReadMem] Endian mismatch:"
                                     , " *** Model: " ++ show have
                                     , " *** Read : " ++ show need ]


