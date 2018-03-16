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
  , runCodeBlock
  -- , runBlocks
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
  , CallHandler
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
import qualified Lang.Crucible.Simulator.Intrinsics as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.RegMap as C
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Symbol(userSymbol)
import           System.IO (stdout)

import qualified Lang.Crucible.LLVM.MemModel as MM
import qualified Lang.Crucible.LLVM.MemModel.Pointer as MM
import qualified Lang.Crucible.LLVM.DataLayout as MM

import qualified Data.Macaw.CFG.Block as M
import qualified Data.Macaw.CFG.Core as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Memory as M
import qualified Data.Macaw.Types as M

import           Data.Macaw.Symbolic.CrucGen
import           Data.Macaw.Symbolic.PersistentState
import           Data.Macaw.Symbolic.MemOps

data MacawSimulatorState sym = MacawSimulatorState

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
             ->  (M.ArchAddrWord arch -> C.Position)
             -- ^ Function that maps offsets from start of block to Crucible position.
             -> [M.Block arch ids]
             -- ^ List of blocks for this region.
             -> MacawMonad arch ids s [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
addBlocksCFG archFns baseAddrMap posFn macawBlocks = do
  crucGenArchConstraints archFns $ do
   -- Map block map to Crucible CFG
  let blockLabelMap :: Map Word64 (CR.Label s)
      blockLabelMap = Map.fromList [ (w, CR.Label (fromIntegral w))
                                   | w <- M.blockLabel <$> macawBlocks ]
  forM macawBlocks $ \b -> do
    addMacawBlock archFns baseAddrMap blockLabelMap posFn b

-- | Create a Crucible CFG from a list of blocks
mkBlocksCFG :: forall s arch ids
            .  MacawSymbolicArchFunctions arch
               -- ^ Crucible specific functions.
            -> C.HandleAllocator s
               -- ^ Handle allocator to make the blocks
            -> MemSegmentMap (M.ArchAddrWidth arch)
               -- ^ Map from region indices to their address
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> (M.ArchAddrWord arch -> C.Position)
            -- ^ Function that maps offsets from start of block to Crucible position.
            -> [M.Block arch ids]
            -- ^ List of blocks for this region.
            -> ST s (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlocksCFG archFns halloc memBaseVarMap nm posFn macawBlocks = do
  mkCrucCFG archFns halloc nm $ do
    addBlocksCFG archFns memBaseVarMap posFn macawBlocks

-- | Create a map from Macaw @(address, index)@ pairs to Crucible labels
mkBlockLabelMap :: [M.ParsedBlock arch ids] -> BlockLabelMap arch s
mkBlockLabelMap blks = fst $ foldl' insBlock (Map.empty,1) blks
 where insBlock :: (BlockLabelMap arch s,Int) -> M.ParsedBlock arch ids -> (BlockLabelMap arch s,Int)
       insBlock m b = insSentences (M.pblockAddr b) m [M.blockStatementList b]

       insSentences :: M.ArchSegmentOff arch
                    -> (BlockLabelMap arch s, Int)
                    -> [M.StatementList arch ids]
                    -> (BlockLabelMap arch s, Int)
       insSentences _ m [] = m
       insSentences base (m,c) (s:r) =
         insSentences base
                      (Map.insert (base,M.stmtsIdent s) (CR.Label c) m,c+1)
                      (nextStatements (M.stmtsTerm s) ++ r)

-- | This create a Crucible CFG from a Macaw `DiscoveryFunInfo` value.
mkFunCFG :: forall s arch ids
         .  MacawSymbolicArchFunctions arch
            -- ^ Architecture specific functions.
         -> C.HandleAllocator s
            -- ^ Handle allocator to make the blocks
         -> MemSegmentMap (M.ArchAddrWidth arch)
            -- ^ Map from region indices to their address
         -> C.FunctionName
            -- ^ Name of function for pretty print purposes.
         -> (M.ArchSegmentOff arch -> C.Position)
            -- ^ Function that maps function address to Crucible position
         -> M.DiscoveryFunInfo arch ids
         -- ^ List of blocks for this region.
         -> ST s (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkFunCFG archFns halloc memBaseVarMap nm posFn fn = crucGenArchConstraints archFns $ do
  mkCrucCFG archFns halloc nm $ do
    -- Get entry point address for function
    let entryAddr = M.discoveredFunAddr fn
    -- Get list of blocks
    let blockList = Map.elems (fn^.M.parsedBlocks)
    -- Get type for representing Machine registers
    let regType = C.StructRepr (crucArchRegTypes archFns)
    let entryPos = posFn entryAddr
    -- Create Crucible "register" (i.e. a mutable variable) for
    -- current value of Macaw machine registers.
    let regReg = CR.Reg { CR.regPosition = entryPos
                        , CR.regId = 0
                        , CR.typeOfReg = regType
                        }
    -- Create atom for entry
    let Empty :> inputAtom = CR.mkInputAtoms entryPos (Empty :> regType)
    -- Create map from Macaw (address,blockId pairs) to Crucible labels
    let blockLabelMap :: BlockLabelMap arch s
        blockLabelMap = mkBlockLabelMap blockList
    -- Get initial block for Crucible
    let entryLabel = CR.Label 0
    let initPosFn :: M.ArchAddrWord arch -> C.Position
        initPosFn off = posFn r
          where Just r = M.incSegmentOff entryAddr (toInteger off)
    (initCrucibleBlock,_) <-
      runCrucGen archFns memBaseVarMap initPosFn 0 entryLabel regReg $ do
        -- Initialize value in regReg with initial registers
        setMachineRegs inputAtom
        -- Jump to function entry point
        addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap entryAddr 0)

    -- Generate code for Macaw blocks after entry
    restCrucibleBlocks <-
      forM blockList $ \b -> do
        addParsedBlock archFns memBaseVarMap blockLabelMap posFn regReg b
    -- Return initialization block followed by actual blocks.
    pure (initCrucibleBlock : concat restCrucibleBlocks)

evalMacawExprExtension :: IsSymInterface sym
                       => sym
                       -> C.IntrinsicTypes sym
                       -> (Int -> String -> IO ())
                       -> (forall utp . f utp -> IO (C.RegValue sym utp))
                       -> MacawExprExtension arch f tp
                       -> IO (C.RegValue sym tp)
evalMacawExprExtension sym _iTypes _logFn f e0 =
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

    PtrToBits  w x  -> doPtrToBits sym w =<< f x
    BitsToPtr _w x  -> MM.llvmPointer_bv sym =<< f x

    MacawNullPtr w | LeqProof <- lemma1_16 w -> MM.mkNullPointer sym w

type EvalStmtFunc f p sym ext =
  forall rtp blocks r ctx tp'.
    f (C.RegEntry sym) tp'
    -> C.CrucibleState p sym ext rtp blocks r ctx
    -> IO (C.RegValue sym tp', C.CrucibleState p sym ext rtp blocks r ctx)

-- | Function for evaluating an architecture-specific statement
type MacawArchEvalFn sym arch =
  EvalStmtFunc (MacawArchStmtExtension arch) MacawSimulatorState sym (MacawExt arch)

type Regs sym arch = Ctx.Assignment (C.RegValue' sym)
                                    (MacawCrucibleRegTypes arch)
type CallHandler sym arch =
     (MM.MemImpl sym, Regs sym arch) -> IO (MM.MemImpl sym, Regs sym arch)

-- | This evaluates a  Macaw statement extension in the simulator.
execMacawStmtExtension ::
  IsSymInterface sym =>
  MacawArchEvalFn sym arch {- ^ Function for executing -} ->
  C.GlobalVar MM.Mem ->
  GlobalMap sym arch ->
  CallHandler sym arch ->
  EvalStmtFunc (MacawStmtExtension arch) MacawSimulatorState sym (MacawExt arch)
execMacawStmtExtension archStmtFn mvar globs callH s0 st =
  case s0 of
    MacawReadMem w mr x         -> doReadMem st mvar globs w mr x
    MacawCondReadMem w mr p x d -> doCondReadMem st mvar globs w mr p x d
    MacawWriteMem w mr x v      -> doWriteMem st mvar globs w mr x v

    MacawGlobalPtr addr         -> doGetGlobal st mvar globs addr

    MacawFreshSymbolic t ->
      do nm <- case userSymbol "macawFresh" of
                 Right a -> return a
                 Left err -> fail (show err)
         v <- case t of
               M.BoolTypeRepr -> freshConstant sym nm C.BaseBoolRepr
               _ -> error ("MacawFreshSymbolic: XXX type " ++ show t)
         return (v,st)
      where sym = C.stateSymInterface st

    MacawCall _ty f -> doMakeCall callH st mvar (C.regValue f)

    MacawArchStmtExtension s    -> archStmtFn s st

    PtrEq  w x y                -> doPtrEq st mvar w x y
    PtrLt  w x y                -> doPtrLt st mvar w x y
    PtrLeq w x y                -> doPtrLeq st mvar w x y
    PtrMux w c x y              -> doPtrMux (C.regValue c) st mvar w x y
    PtrAdd w x y                -> doPtrAdd st mvar w x y
    PtrSub w x y                -> doPtrSub st mvar w x y


-- | Return macaw extension evaluation functions.
macawExtensions ::
  IsSymInterface sym =>
  MacawArchEvalFn sym arch ->
  C.GlobalVar MM.Mem ->
  GlobalMap sym arch ->
  CallHandler sym arch ->
  C.ExtensionImpl MacawSimulatorState sym (MacawExt arch)
macawExtensions f mvar globs callH =
  C.ExtensionImpl { C.extensionEval = evalMacawExprExtension
                  , C.extensionExec = execMacawStmtExtension f mvar globs callH
                  }


-- | Maps region indexes to the pointers representing them.
type GlobalMap sym arch = Map M.RegionIndex
                              (MM.LLVMPtr sym (M.ArchAddrWidth arch))



-- | Run the simulator over a contiguous set of code.
runCodeBlock :: forall sym arch blocks
           .  IsSymInterface sym
           => sym
           -> MacawSymbolicArchFunctions arch
              -- ^ Translation functions
           -> MacawArchEvalFn sym arch
           -> C.HandleAllocator RealWorld
           -> (MM.MemImpl sym, GlobalMap sym arch)
           -> CallHandler sym arch
           -> C.CFG (MacawExt arch) blocks (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch)
           -> Ctx.Assignment (C.RegValue' sym) (MacawCrucibleRegTypes arch)
              -- ^ Register assignment
           -> IO ( C.GlobalVar MM.Mem
                 , C.ExecResult
                   MacawSimulatorState
                   sym
                   (MacawExt arch)
                   (C.RegEntry sym (ArchRegStruct arch)))
runCodeBlock sym archFns archEval halloc (initMem,globs) callH g regStruct = do
  mvar <- stToIO (MM.mkMemVar halloc)
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
                         , C.extensionImpl = macawExtensions archEval mvar globs
                                                          callH
                         , C._functionBindings =
                              C.insertHandleMap (C.cfgHandle g) (C.UseCFG g (C.postdomInfo g)) $
                              C.emptyHandleMap
                         , C._cruciblePersonality = MacawSimulatorState
                         }
  -- Create the symbolic simulator state
  let initGlobals = C.insertGlobal mvar initMem C.emptyGlobals
  let s = C.initSimState ctx initGlobals C.defaultErrorHandler
  a <- C.runOverrideSim s macawStructRepr $ do
    let args :: C.RegMap sym (MacawFunctionArgs arch)
        args = C.RegMap (Ctx.singleton (C.RegEntry macawStructRepr regStruct))
    crucGenArchConstraints archFns $
      C.regValue <$> C.callCFG g args
  return (mvar,a)

{-
-- | Run the simulator over a contiguous set of code.
-- NOTE: this is probably not the function that shuold be called,
-- as it has no way to initialize memory.
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
  C.SomeCFG g <- stToIO $ mkBlocksCFG archFns halloc memBaseVarMap nm posFn macawBlocks
  mvar <- stToIO $ MM.mkMemVar halloc
  initMem <- MM.emptyMem MM.LittleEndian
  -- Run the symbolic simulator.
  runCodeBlock sym archFns archEval halloc (mvar,initMem) g regStruct
-}
