{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PatternGuards #-}
module Data.Macaw.Symbolic
  ( Data.Macaw.Symbolic.CrucGen.MacawSymbolicArchFunctions(..)
  , Data.Macaw.Symbolic.CrucGen.CrucGen
  , Data.Macaw.Symbolic.CrucGen.MemSegmentMap
  , MacawSimulatorState
  -- , freshVarsForRegs
  , runCodeBlock
  , runBlocks
  , mkBlocksCFG
  , mkFunCFG
  , Data.Macaw.Symbolic.PersistentState.ArchRegContext
  , Data.Macaw.Symbolic.PersistentState.ToCrucibleType
  , Data.Macaw.Symbolic.PersistentState.macawAssignToCrucM
  , Data.Macaw.Symbolic.CrucGen.ArchRegStruct
  , Data.Macaw.Symbolic.CrucGen.MacawCrucibleRegTypes
  , Data.Macaw.Symbolic.CrucGen.valueToCrucible
  , Data.Macaw.Symbolic.CrucGen.evalArchStmt
    -- * Architecture-specific extensions
  , Data.Macaw.Symbolic.CrucGen.MacawArchStmtExtension
  , Data.Macaw.Symbolic.CrucGen.MacawArchConstraints
  , MacawArchEvalFn
  , EvalStmtFunc
  ) where

import           Control.Lens ((^.))
import           Control.Monad (forM, join)
import           Control.Monad.ST (ST, RealWorld, stToIO)
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Set as Set
import qualified Data.Text as Text
import           Data.Word
import qualified Lang.Crucible.Analysis.Postdom as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.CFG.SSAConversion as C
import qualified Lang.Crucible.Config as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.FunctionName as C
import qualified Lang.Crucible.ProgramLoc as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C
import           Lang.Crucible.Solver.Interface
import           System.IO (stdout)

import qualified Lang.Crucible.LLVM.MemModel as MM
import qualified Lang.Crucible.LLVM.MemModel.Pointer as MM

import qualified Data.Macaw.CFG.Block as M
import qualified Data.Macaw.CFG.Core as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Memory as M

import           Data.Macaw.Symbolic.CrucGen
import           Data.Macaw.Symbolic.PersistentState

data MacawSimulatorState sym = MacawSimulatorState

{-
-- | Create the variables from a collection of registers.
freshVarsForRegs :: (IsSymInterface sym, M.HasRepr reg M.TypeRepr)
                 => sym
                 -> (forall tp . reg tp -> SolverSymbol)
                 -> Ctx.Assignment reg ctx
                 -> IO (Ctx.Assignment (C.RegValue' sym) (CtxToCrucibleType ctx))
freshVarsForRegs sym nameFn a =
  case a of
    Empty -> pure Ctx.empty
    b :> reg -> do
      varAssign <- freshVarsForRegs sym nameFn b
      c <- freshConstant sym (nameFn reg) (typeToCrucibleBase (M.typeRepr reg))
      pure (varAssign :> C.RV c)
#if !MIN_VERSION_base(4,10,0)
    _ -> error "internal: freshVarsForRegs encountered case non-exhaustive pattern"
#endif
-}

mkMemSegmentBinding :: (1 <= w)
                    => C.HandleAllocator s
                    -> NatRepr w
                    -> M.RegionIndex
                    -> ST s (M.RegionIndex, C.GlobalVar (C.BVType w))
mkMemSegmentBinding halloc awidth idx = do
  let nm = Text.pack ("MemSegmentBase" ++ show idx)
  gv <- CR.freshGlobalVar halloc nm (C.BVRepr awidth)
  pure $ (idx, gv)

mkMemBaseVarMap :: (1 <= w)
                => C.HandleAllocator s
                -> M.Memory w
                -> ST s (MemSegmentMap w)
mkMemBaseVarMap halloc mem = do
  let baseIndices = Set.fromList
        [ M.segmentBase seg
        | seg <- M.memSegments mem
        , M.segmentBase seg /= 0
        ]
  Map.fromList <$> traverse (mkMemSegmentBinding halloc (M.memWidth mem)) (Set.toList baseIndices)

-- | Create a Crucible CFG from a list of blocks
mkCrucCFG :: forall s arch ids
            .  MacawSymbolicArchFunctions arch
               -- ^ Crucible architecture-specific functions.
            -> C.HandleAllocator s
               -- ^ Handle allocator to make function handles
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> MacawMonad arch ids s [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
                -- ^ Action to run
            -> ST s (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkCrucCFG archFns halloc nm action = do
  let crucRegTypes = crucArchRegTypes archFns
  let macawStructRepr = C.StructRepr crucRegTypes
  let argTypes = Empty :> macawStructRepr
  h <- C.mkHandle' halloc nm argTypes macawStructRepr
  let ps0 = initCrucPersistentState 1
  blockRes <- runMacawMonad ps0 action
  blks <-
    case blockRes of
      (Left err, _) -> fail err
      (Right blks, _)  -> pure blks
  -- Create control flow graph
  let rg :: CR.CFG (MacawExt arch) s (MacawFunctionArgs arch) (MacawFunctionResult arch)
      rg = CR.CFG { CR.cfgHandle = h
                  , CR.cfgBlocks = blks
                  }
  crucGenArchConstraints archFns $
    pure $ C.toSSA rg

-- | Create a Crucible CFG from a list of blocks
addBlocksCFG :: forall s arch ids
             .  MacawSymbolicArchFunctions arch
             -- ^ Crucible specific functions.
             -> MemSegmentMap (M.ArchAddrWidth arch)
             -- ^ Base address map
             -> C.GlobalVar MM.Mem
             -- ^ Memory
             ->  (M.ArchAddrWord arch -> C.Position)
             -- ^ Function that maps offsets from start of block to Crucible position.
             -> [M.Block arch ids]
             -- ^ List of blocks for this region.
             -> MacawMonad arch ids s [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
addBlocksCFG archFns baseAddrMap mem posFn macawBlocks = do
  crucGenArchConstraints archFns $ do
   -- Map block map to Crucible CFG
  let blockLabelMap :: Map Word64 (CR.Label s)
      blockLabelMap = Map.fromList [ (w, CR.Label (fromIntegral w))
                                   | w <- M.blockLabel <$> macawBlocks ]
  forM macawBlocks $ \b -> do
    addMacawBlock archFns baseAddrMap mem blockLabelMap posFn b

-- | Create a Crucible CFG from a list of blocks
mkBlocksCFG :: forall s arch ids
            .  MacawSymbolicArchFunctions arch
               -- ^ Crucible specific functions.
            -> C.HandleAllocator s
               -- ^ Handle allocator to make the blocks
            -> MemSegmentMap (M.ArchAddrWidth arch)
               -- ^ Map from region indices to their address
            -> C.GlobalVar MM.Mem
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> (M.ArchAddrWord arch -> C.Position)
            -- ^ Function that maps offsets from start of block to Crucible position.
            -> [M.Block arch ids]
            -- ^ List of blocks for this region.
            -> ST s (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlocksCFG archFns halloc memBaseVarMap mem nm posFn macawBlocks = do
  mkCrucCFG archFns halloc nm $ do
    addBlocksCFG archFns memBaseVarMap mem posFn macawBlocks

mkFunCFG :: forall s arch ids
         .  MacawSymbolicArchFunctions arch
            -- ^ Architecture specific functions.
         -> C.HandleAllocator s
            -- ^ Handle allocator to make the blocks
         -> MemSegmentMap (M.ArchAddrWidth arch)
            -- ^ Map from region indices to their address
         -> C.GlobalVar MM.Mem
            -- ^ Memory
         -> C.FunctionName
            -- ^ Name of function for pretty print purposes.
         -> (M.ArchSegmentOff arch -> C.Position)
            -- ^ Function that maps function address to Crucible position
         -> M.DiscoveryFunInfo arch ids
         -- ^ List of blocks for this region.
         -> ST s (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkFunCFG archFns halloc memBaseVarMap mem nm posFn fn = do
  mkCrucCFG archFns halloc nm $ do
    let insSentences :: M.ArchSegmentOff arch
                     -> (BlockLabelMap arch s,Int)
                     -> [M.StatementList arch ids]
                     -> (BlockLabelMap arch s,Int)
        insSentences _ m [] = m
        insSentences base (m,c) (s:r) =
          insSentences base
                       (Map.insert (base,M.stmtsIdent s) (CR.Label c) m,c+1)
                       (nextStatements (M.stmtsTerm s) ++ r)
    let insBlock :: (BlockLabelMap arch s,Int) -> M.ParsedBlock arch ids -> (BlockLabelMap arch s,Int)
        insBlock m b = insSentences (M.pblockAddr b) m [M.blockStatementList b]
    let blockLabelMap :: BlockLabelMap arch s
        blockLabelMap = fst $ foldl' insBlock (Map.empty,0) (Map.elems (fn^.M.parsedBlocks))
    let regReg = CR.Reg { CR.regPosition = posFn (M.discoveredFunAddr fn)
                        , CR.regId = 0
                        , CR.typeOfReg = C.StructRepr (crucArchRegTypes archFns)
                        }
    fmap concat $
      forM (Map.elems (fn^.M.parsedBlocks)) $ \b -> do
        -- TODO: Initialize value in regReg with initial registers
        addParsedBlock archFns memBaseVarMap mem blockLabelMap posFn regReg b

evalMacawExprExtension :: IsSymInterface sym
                       => sym
                       -> (forall utp . f utp -> IO (C.RegValue sym utp))
                       -> MacawExprExtension arch f tp
                       -> IO (C.RegValue sym tp)
evalMacawExprExtension sym f e0 =
  case e0 of

    MacawOverflows op w xv yv cv -> do
      x <- f xv
      y <- f yv
      c <- f cv
      let w' = incNat w
      Just LeqProof <- pure $ testLeq (knownNat :: NatRepr 1) w'
      one  <- bvLit sym w' 1
      zero <- bvLit sym w' 0
      cext <- baseTypeIte sym c one zero
      case op of
        Uadc -> do
          -- Unsigned add overflow occurs if largest bit is set.
          xext <- bvZext sym w' x
          yext <- bvZext sym w' y
          zext <- join $ bvAdd sym <$> bvAdd sym xext yext <*> pure cext
          bvIsNeg sym zext
        Sadc -> do
          xext <- bvSext sym w' x
          yext <- bvSext sym w' y
          zext <- join $ bvAdd sym <$> bvAdd sym xext yext <*> pure cext
          znorm <- bvSext sym w' =<< bvTrunc sym w zext
          bvNe sym zext znorm
        Usbb -> do
          xext <- bvZext sym w' x
          yext <- bvZext sym w' y
          zext <- join $ bvSub sym <$> bvSub sym xext yext <*> pure cext
          bvIsNeg sym zext
        Ssbb -> do
          xext <- bvSext sym w' x
          yext <- bvSext sym w' y
          zext <- join $ bvSub sym <$> bvSub sym xext yext <*> pure cext
          znorm <- bvSext sym w' =<< bvTrunc sym w zext
          bvNe sym zext znorm

    PtrToBits _w x  -> MM.projectLLVM_bv sym =<< f x
    BitsToPtr _w x  -> MM.llvmPointer_bv sym =<< f x

-- | Is this value a bit-vector (i.e., not a pointer).
-- Note that the NULL pointer is actually also a bit-vector.
isBitVec :: IsSymInterface sym => sym -> MM.LLVMPtr sym w -> IO (Pred sym)
isBitVec sym (MM.LLVMPointer b _) = natEq sym b =<< natLit sym 0


asBits :: MM.LLVMPtr sym w -> C.RegValue sym (C.BVType w)
asBits = snd . MM.llvmPointerView

ptrBase :: MM.LLVMPtr sym w -> C.RegValue sym C.NatType
ptrBase = fst . MM.llvmPointerView


-- | Classify the arguments, and continue.
ptrOp :: 
  (IsSymInterface sym, 16 <= w) =>
  C.CrucibleState MacawSimulatorState sym ext rtp blocks r ctx ->
  -- ^ The simulator state

  C.GlobalVar MM.Mem      {- ^ Memory -} ->
  NatRepr w               {- ^ Pointer width -} ->
  C.RegEntry sym (MM.LLVMPointerType w)        {- ^ Value 1 -} ->
  C.RegEntry sym (MM.LLVMPointerType w)        {- ^ Value 2 -} ->
  (sym -> C.RegValue sym MM.Mem ->
      Pred sym -> Pred sym -> Pred sym -> Pred sym ->
      MM.LLVMPtr sym w -> MM.LLVMPtr sym w -> IO a) ->
  IO (a, C.CrucibleState MacawSimulatorState sym ext rtp blocks r ctx)

ptrOp st mvar w x0 y0 k =
  do mem      <- getMem mvar st
     LeqProof <- return (lemma1_16 w)
     let sym = C.stateSymInterface st
         x   = C.regValue x0
         y   = C.regValue y0
     xPtr     <- let ?ptrWidth = w in MM.isValidPointer sym x mem
     yPtr     <- let ?ptrWidth = w in MM.isValidPointer sym y mem
     xBits    <- isBitVec sym x
     yBits    <- isBitVec sym x
     a <- k sym mem xPtr xBits yPtr yBits x y
     return (a,st)




-- | Do a binary operation on bit-vector/pointers, where both arguments
-- must be valid pointers or both argumnets must be bit-vectors.
ptr2 ::
  (IsSymInterface sym, 16 <= w) =>
  C.CrucibleState MacawSimulatorState sym ext rtp blocks r ctx ->
  -- ^ The simulator state

  C.GlobalVar MM.Mem      {- ^ Memory -} ->
  NatRepr w               {- ^ Pointer width -} ->


  String                  {- ^ Name of operation (for error reporting) -} ->
  C.RegEntry sym (MM.LLVMPointerType w)        {- ^ Value 1 -} ->
  C.RegEntry sym (MM.LLVMPointerType w)        {- ^ Value 2 -} ->

  -- | Mux the results
  (sym -> C.RegValue sym C.BoolType -> a -> a -> IO a) ->

  -- | Operation to use for bit-vector version
  (sym -> C.RegValue sym (C.BVType w) -> C.RegValue sym (C.BVType w) -> IO a) ->

  -- | Operation to use for pointer version
  (sym -> NatRepr w -> MM.LLVMPtr sym w -> MM.LLVMPtr sym w -> IO a) ->
  IO (a, C.CrucibleState MacawSimulatorState sym ext rtp blocks r ctx)
ptr2 st mvar w nm x0 y0 mux ifBits ifPtr =
  ptrOp st mvar w x0 y0 $ \sym _ xPtr xBits yPtr yBits x y ->
  do bothPtrs <- andPred sym xPtr yPtr
     bothBits <- andPred sym xBits yBits
     ok       <- orPred sym bothPtrs bothBits
     addAssertion sym ok
       (C.AssertFailureSimError ("Invalid arguments to " ++ nm))
     ptrRes <- ifPtr sym w x y
     bitRes <- ifBits sym (asBits x) (asBits y)
     mux sym bothPtrs ptrRes bitRes


-- | Get the current model of the memory.
getMem :: C.GlobalVar MM.Mem ->
          C.CrucibleState MacawSimulatorState sym ext rtp blocks r ctx ->
          IO (C.RegValue sym MM.Mem)
getMem mvar st =
  case C.lookupGlobal mvar (st ^. C.stateTree . C.actFrame . C.gpGlobals) of
    Just mem -> return mem
    Nothing  -> fail ("Global heap value not initialized: " ++ show mvar)


type EvalStmtFunc f p sym ext =
  forall rtp blocks r ctx tp'.
    f (C.RegEntry sym) tp'
    -> C.CrucibleState p sym ext rtp blocks r ctx
    -> IO (C.RegValue sym tp', C.CrucibleState p sym ext rtp blocks r ctx)

-- | Function for evaluating an architecture-specific statement
type MacawArchEvalFn sym arch =
  EvalStmtFunc (MacawArchStmtExtension arch) MacawSimulatorState sym (MacawExt arch)

-- | This evaluates a  Macaw statement extension in the simulator.
execMacawStmtExtension ::
  IsSymInterface sym =>
  MacawArchEvalFn sym arch {- ^ Function for executing -} ->
  EvalStmtFunc (MacawStmtExtension arch) MacawSimulatorState sym (MacawExt arch)
execMacawStmtExtension archStmtFn s0 st =
  case s0 of
    MacawReadMem{} -> undefined
    MacawCondReadMem{} -> undefined
    MacawWriteMem{} -> undefined
    MacawFreshSymbolic{} -> undefined
    MacawCall{} -> undefined
    MacawArchStmtExtension s -> archStmtFn s st

    PtrEq mem w x y | LeqProof <- lemma1_16 w ->
      ptr2 st mem w "ptr_eq" x y itePred bvEq MM.ptrEq

    PtrLt mvar w x0 y0 | LeqProof <- lemma1_16 w ->
      ptrOp st mvar w x0 y0 $ \sym _ xPtr xBits yPtr yBits x y ->
        do both_bits <- andPred sym xBits yBits
           both_ptrs <- andPred sym xPtr  yPtr
           sameRegion <- natEq sym (ptrBase x) (ptrBase y)
           ok <- andPred sym sameRegion =<< orPred sym both_bits both_ptrs
           addAssertion sym ok
             (C.AssertFailureSimError "Invalid arguments to ptr_lt")
           bvUlt sym (asBits x) (asBits y)

    PtrLeq mvar w x0 y0 | LeqProof <- lemma1_16 w ->
      ptrOp st mvar w x0 y0 $ \sym _ xPtr xBits yPtr yBits x y ->
        do both_bits <- andPred sym xBits yBits
           both_ptrs <- andPred sym xPtr  yPtr
           sameRegion <- natEq sym (ptrBase x) (ptrBase y)
           ok <- andPred sym sameRegion =<< orPred sym both_bits both_ptrs
           addAssertion sym ok
             (C.AssertFailureSimError "Invalid arguments to ptr_leq")
           bvUle sym (asBits x) (asBits y)

    PtrMux mem w c x y | LeqProof <- lemma1_16 w ->
      do let ifBits sym a b = do r <- bvIte sym (C.regValue c) a b
                                 MM.llvmPointer_bv sym r
             ifPtr sym _ a b = MM.muxLLVMPtr sym (C.regValue c) a b
         ptr2 st mem w "ptr_mux" x y MM.muxLLVMPtr ifBits ifPtr

    PtrAdd mvar w x0 y0 | LeqProof <- lemma1_16 w ->
      ptrOp st mvar w x0 y0 $ \sym mem xPtr xBits yPtr yBits x y ->
        do both_bits <- andPred sym xBits yBits     -- (1)
           ptr_bits  <- andPred sym xPtr yBits   -- (2)
           bits_ptr  <- andPred sym xBits yPtr   -- (3)
           ok        <- orPred sym both_bits =<< orPred sym ptr_bits bits_ptr
           addAssertion sym ok
             (C.AssertFailureSimError "Invalid arguments to ptr_add")

           case1 <- MM.llvmPointer_bv sym =<< bvAdd sym (asBits x) (asBits y)

           case2    <- MM.ptrAdd sym w x (asBits y)
           valid2   <- let ?ptrWidth = w in MM.isValidPointer sym case2 mem
           case2_ok <- impliesPred sym ptr_bits valid2
           addAssertion sym case2_ok
             (C.AssertFailureSimError "Invalid result of ptr_add")

           case3 <- MM.ptrAdd sym w y (asBits x)
           valid3 <- let ?ptrWidth = w in MM.isValidPointer sym case3 mem
           case3_ok <- impliesPred sym bits_ptr valid3
           addAssertion sym case3_ok
             (C.AssertFailureSimError "Invalid result of ptr_add")

           case23 <- MM.muxLLVMPtr sym ptr_bits case2 case3
           MM.muxLLVMPtr sym both_bits case1 case23


    PtrSub mvar w x0 y0 | LeqProof <- lemma1_16 w ->
      ptrOp st mvar w x0 y0 $ \sym mem xPtr xBits yPtr yBits x y ->
        do both_bits <- andPred sym xBits yBits    -- (1)
           ptr_bits  <- andPred sym xPtr  yBits    -- (2)
           ptr_ptr   <- andPred sym xPtr  yPtr     -- (3)
           ok <- orPred sym ptr_ptr =<< orPred sym both_bits ptr_bits
           addAssertion sym ok
             (C.AssertFailureSimError "Invalid arguments to ptr_sub")

           case1 <- MM.llvmPointer_bv sym =<< bvSub sym (asBits x) (asBits y)

           case2 <- MM.ptrSub sym w x (asBits y)
           valid2 <- let?ptrWidth = w in MM.isValidPointer sym case2 mem
           case2_ok <- impliesPred sym ptr_bits valid2
           addAssertion sym case2_ok
             (C.AssertFailureSimError "Invalid result of ptr_sub")

           case3    <- MM.llvmPointer_bv sym =<< bvSub sym (asBits x) (asBits y)
           valid3   <- natEq sym (ptrBase x) (ptrBase y)
           case3_ok <- impliesPred sym ptr_ptr valid3
           addAssertion sym case3_ok
             (C.AssertFailureSimError
                "Cannot subtract pointers from different allocation.")

           case23 <- MM.muxLLVMPtr sym ptr_bits case2 case3
           MM.muxLLVMPtr sym both_bits case1 case23


-- | Return macaw extension evaluation functions.
macawExtensions ::
  IsSymInterface sym =>
  MacawArchEvalFn sym arch ->
  C.ExtensionImpl MacawSimulatorState sym (MacawExt arch)
macawExtensions f =
  C.ExtensionImpl { C.extensionEval = evalMacawExprExtension
                  , C.extensionExec = execMacawStmtExtension f
                  }

-- | Run the simulator over a contiguous set of code.
runCodeBlock :: forall sym arch blocks
           .  IsSymInterface sym
           => sym
           -> MacawSymbolicArchFunctions arch
              -- ^ Translation functions
           -> MacawArchEvalFn sym arch
           -> C.HandleAllocator RealWorld
           -> C.CFG (MacawExt arch) blocks (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch)
           -> Ctx.Assignment (C.RegValue' sym) (MacawCrucibleRegTypes arch)
              -- ^ Register assignment
           -> IO (C.ExecResult
                   MacawSimulatorState
                   sym
                   (MacawExt arch)
                   (C.RegEntry sym (ArchRegStruct arch)))
runCodeBlock sym archFns archEval halloc g regStruct = do
  let crucRegTypes = crucArchRegTypes archFns
  let macawStructRepr = C.StructRepr crucRegTypes
  -- Run the symbolic simulator.
  cfg <- C.initialConfig 0 []
  let ctx :: C.SimContext MacawSimulatorState sym (MacawExt arch)
      ctx = C.SimContext { C._ctxSymInterface = sym
                         , C.ctxSolverProof = \a -> a
                         , C.ctxIntrinsicTypes = MapF.empty
                         , C.simConfig = cfg
                         , C.simHandleAllocator = halloc
                         , C.printHandle = stdout
                         , C.extensionImpl = macawExtensions archEval
                         , C._functionBindings =
                              C.insertHandleMap (C.cfgHandle g) (C.UseCFG g (C.postdomInfo g)) $
                              C.emptyHandleMap
                         , C._cruciblePersonality = MacawSimulatorState
                         }
  -- Create the symbolic simulator state
  let s = C.initSimState ctx C.emptyGlobals C.defaultErrorHandler
  C.runOverrideSim s macawStructRepr $ do
    let args :: C.RegMap sym (MacawFunctionArgs arch)
        args = C.RegMap (Ctx.singleton (C.RegEntry macawStructRepr regStruct))
    crucGenArchConstraints archFns $
      C.regValue <$> C.callCFG g args

-- | Run the simulator over a contiguous set of code.
runBlocks :: forall sym arch ids
           .  (IsSymInterface sym, M.ArchConstraints arch)
           => sym
           -> MacawSymbolicArchFunctions arch
              -- ^ Crucible specific functions.
           -> MacawArchEvalFn sym arch
           -> M.Memory (M.ArchAddrWidth arch)
              -- ^ Memory image for executable
           -> C.FunctionName
              -- ^ Name of function for pretty print purposes.
           -> (M.ArchAddrWord arch -> C.Position)
              -- ^ Function that maps offsets from start of block to Crucible position.
           -> [M.Block arch ids]
              -- ^ List of blocks for this region.
           -> Ctx.Assignment (C.RegValue' sym)
                             (CtxToCrucibleType (ArchRegContext arch))
              -- ^ Register assignment
           -> IO (C.ExecResult
                   MacawSimulatorState
                   sym
                   (MacawExt arch)
                   (C.RegEntry sym (C.StructType
                              (CtxToCrucibleType (ArchRegContext arch)))))
runBlocks sym archFns archEval mem nm posFn macawBlocks regStruct = do
  halloc <- C.newHandleAllocator
  memBaseVarMap <- stToIO $ mkMemBaseVarMap halloc mem
  mvar <- stToIO (MM.mkMemVar halloc)
  C.SomeCFG g <- stToIO $ mkBlocksCFG archFns halloc memBaseVarMap mvar nm posFn macawBlocks
  -- Run the symbolic simulator.
  runCodeBlock sym archFns archEval halloc g regStruct
