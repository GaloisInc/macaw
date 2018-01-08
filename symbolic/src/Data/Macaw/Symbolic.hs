{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.Symbolic
  ( Data.Macaw.Symbolic.CrucGen.CrucGenArchFunctions(..)
  , Data.Macaw.Symbolic.CrucGen.CrucGen
  , MacawSimulatorState
  , freshVarsForRegs
  , runCodeBlock
  , runBlocks
  , mkBlocksCFG
  , mkFunCFG
  , Data.Macaw.Symbolic.PersistentState.ArchRegContext
  , Data.Macaw.Symbolic.PersistentState.ToCrucibleType
  , Data.Macaw.Symbolic.PersistentState.UsedHandleSet
  ) where

import           Control.Lens ((^.))
import           Control.Monad (forM)
import           Control.Monad.ST (ST, RealWorld, stToIO)
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableFC
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
import           Lang.Crucible.Solver.Interface
import           System.IO (stdout)

import qualified Data.Macaw.CFG.Block as M
import qualified Data.Macaw.CFG.Core as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Memory as M
import qualified Data.Macaw.Types as M

import           Data.Macaw.Symbolic.CrucGen
import           Data.Macaw.Symbolic.PersistentState

data MacawSimulatorState sym = MacawSimulatorState

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

-- | An override that creates a fresh value with the given type.
runFreshSymOverride :: M.TypeRepr tp
                    -> C.OverrideSim MacawSimulatorState sym MacawExt ret
                                     EmptyCtx
                                     (ToCrucibleType tp)
                                     (C.RegValue sym (ToCrucibleType tp))
runFreshSymOverride tp = do
  undefined tp

-- | Run override that reads a value from memory.
runReadMemOverride :: M.AddrWidthRepr w -- ^ Width of the address.
                   -> M.MemRepr tp -- ^ Type of value to read.
                   -> C.OverrideSim MacawSimulatorState sym MacawExt ret
                                    (EmptyCtx ::> C.BVType w)
                                    (ToCrucibleType tp)
                                    (C.RegValue sym (ToCrucibleType tp))
runReadMemOverride = undefined

-- | Run override that writes a value to memory.
runWriteMemOverride :: M.AddrWidthRepr w -- ^ Width of a pointer
                    -> M.MemRepr tp      -- ^ Type of value to write to memory.
                    -> C.OverrideSim MacawSimulatorState sym MacawExt ret
                                     (EmptyCtx ::> C.BVType w ::> ToCrucibleType tp)
                                     C.UnitType
                                     (C.RegValue sym C.UnitType)
runWriteMemOverride = undefined

createHandleBinding :: M.AddrWidthRepr (M.ArchAddrWidth arch)
                    -> HandleId arch '(args, rtp)
                    -> C.OverrideSim MacawSimulatorState sym MacawExt ret args rtp (C.RegValue sym rtp)
createHandleBinding w hid =
  case hid of
    MkFreshSymId repr -> runFreshSymOverride repr
    ReadMemId repr    -> runReadMemOverride w repr
    WriteMemId repr   -> runWriteMemOverride w repr

-- | This function identifies all the handles needed, and returns
-- function bindings for each one.
createHandleMap :: forall arch sym
                .  M.AddrWidthRepr (M.ArchAddrWidth arch)
                -> UsedHandleSet arch
                -> C.FunctionBindings MacawSimulatorState sym MacawExt
createHandleMap w = MapF.foldrWithKey go C.emptyHandleMap
  where go :: HandleId arch pair
           -> HandleVal pair
           -> C.FunctionBindings MacawSimulatorState sym MacawExt
           -> C.FunctionBindings MacawSimulatorState sym MacawExt
        go hid (HandleVal h) b =
          let o = C.mkOverride' (handleIdName hid) (handleIdRetType hid) (createHandleBinding w hid)
           in  C.insertHandleMap h (C.UseOverride o) b

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
            .  M.ArchConstraints arch
            => C.HandleAllocator s
               -- ^ Handle allocator to make function handles
            -> CrucGenArchFunctions arch
               -- ^ Crucible architecture-specific functions.
            -> MemSegmentMap (M.ArchAddrWidth arch)
               -- ^ Map from region indices to their address
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> (CrucGenContext arch s
                 -> MacawMonad arch ids s [CR.Block MacawExt s (MacawFunctionResult arch)])
                -- ^ Action to run
            -> ST s ( UsedHandleSet arch
                    , C.SomeCFG MacawExt (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch)
                    )
mkCrucCFG halloc archFns memBaseVarMap nm action = do
  let regAssign = crucGenRegAssignment archFns
  let crucRegTypes = typeCtxToCrucible (fmapFC M.typeRepr regAssign)
  let macawStructRepr = C.StructRepr crucRegTypes
  let argTypes = Empty :> macawStructRepr
  h <- C.mkHandle' halloc nm argTypes macawStructRepr
  let genCtx = CrucGenContext { archConstraints = \x -> x
                              , macawRegAssign = regAssign
                              , regIndexMap = mkRegIndexMap regAssign (Ctx.size crucRegTypes)
                              , handleAlloc = halloc
                              , memBaseAddrMap = memBaseVarMap
                              }
  let ps0 = initCrucPersistentState
  blockRes <- runMacawMonad ps0 (action genCtx)
  (blks, ps) <-
    case blockRes of
      (Left err, _) -> fail err
      (Right blks, s)  -> pure (blks, s)
  -- Create control flow graph
  let rg :: CR.CFG MacawExt s (MacawFunctionArgs arch) (MacawFunctionResult arch)
      rg = CR.CFG { CR.cfgHandle = h
                  , CR.cfgBlocks = blks
                  }
  pure $ (handleMap ps, C.toSSA rg)

-- | Create a Crucible CFG from a list of blocks
addBlocksCFG :: forall s arch ids
            .  M.ArchConstraints arch
            => CrucGenArchFunctions arch
               -- ^ Crucible specific functions.
            -> CrucGenContext arch s
            -> (M.ArchAddrWord arch -> C.Position)
            -- ^ Function that maps offsets from start of block to Crucible position.
            -> [M.Block arch ids]
            -- ^ List of blocks for this region.
            -> MacawMonad arch ids s [CR.Block MacawExt s (MacawFunctionResult arch)]
addBlocksCFG archFns ctx posFn macawBlocks = do
  -- Map block map to Crucible CFG
  let blockLabelMap :: Map Word64 (CR.Label s)
      blockLabelMap = Map.fromList [ (w, CR.Label (fromIntegral w))
                                   | w <- M.blockLabel <$> macawBlocks ]
  forM macawBlocks $ \b -> do
    addMacawBlock archFns ctx blockLabelMap posFn b

-- | Create a Crucible CFG from a list of blocks
mkBlocksCFG :: forall s arch ids
            .  M.ArchConstraints arch
            => C.HandleAllocator s
               -- ^ Handle allocator to make the blocks
            -> CrucGenArchFunctions arch
               -- ^ Crucible specific functions.
            -> MemSegmentMap (M.ArchAddrWidth arch)
               -- ^ Map from region indices to their address
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> (M.ArchAddrWord arch -> C.Position)
            -- ^ Function that maps offsets from start of block to Crucible position.
            -> [M.Block arch ids]
            -- ^ List of blocks for this region.
            -> ST s ( UsedHandleSet arch
                    , C.SomeCFG MacawExt (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch)
                    )
mkBlocksCFG halloc archFns memBaseVarMap nm posFn macawBlocks = do
  mkCrucCFG halloc archFns memBaseVarMap nm $ \ctx -> do
    addBlocksCFG archFns ctx posFn macawBlocks

type FunBlockMap arch s = Map (M.ArchSegmentOff arch, Word64) (CR.Label s)

mkFunCFG :: forall s arch ids
         .  M.ArchConstraints arch
         => C.HandleAllocator s
            -- ^ Handle allocator to make the blocks
         -> CrucGenArchFunctions arch
            -- ^ Crucible specific functions.
         -> MemSegmentMap (M.ArchAddrWidth arch)
            -- ^ Map from region indices to their address
         -> C.FunctionName
            -- ^ Name of function for pretty print purposes.
         -> (M.ArchSegmentOff arch -> C.Position)
            -- ^ Function that maps function address to Crucible position
         -> M.DiscoveryFunInfo arch ids
         -- ^ List of blocks for this region.
         -> ST s ( UsedHandleSet arch
                 , C.SomeCFG MacawExt (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch)
                 )
mkFunCFG halloc archFns memBaseVarMap nm posFn fn = do
  mkCrucCFG halloc archFns memBaseVarMap nm $ \ctx -> do
    let insSentences :: M.ArchSegmentOff arch
                     -> (FunBlockMap arch s,Int)
                     -> [M.StatementList arch ids]
                     -> (FunBlockMap arch s,Int)
        insSentences _ m [] = m
        insSentences base (m,c) (s:r) =
          insSentences base
                       (Map.insert (base,M.stmtsIdent s) (CR.Label c) m,c+1)
                       (nextStatements (M.stmtsTerm s) ++ r)
    let insBlock :: (FunBlockMap arch s,Int) -> M.ParsedBlock arch ids -> (FunBlockMap arch s,Int)
        insBlock m b = insSentences (M.pblockAddr b) m [M.blockStatementList b]
    let blockLabelMap :: FunBlockMap arch s
        blockLabelMap = fst $ foldl' insBlock (Map.empty,0) (Map.elems (fn^.M.parsedBlocks))
    fmap concat $
      forM (Map.elems (fn^.M.parsedBlocks)) $ \b -> do
        addParsedBlock archFns ctx blockLabelMap posFn b

-- | Run the simulator over a contiguous set of code.
runCodeBlock :: forall sym arch blocks
           .  (IsSymInterface sym, M.ArchConstraints arch)
           => sym
           -> CrucGenArchFunctions arch
           -> C.HandleAllocator RealWorld
           -> UsedHandleSet arch
              -- ^ Handle map
           -> C.CFG MacawExt blocks (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch)
           -> Ctx.Assignment (C.RegValue' sym) (ArchCrucibleRegTypes arch)
              -- ^ Register assignment
           -> IO (C.ExecResult
                   MacawSimulatorState
                   sym
                   MacawExt
                   (C.RegEntry sym (ArchRegStruct arch)))
runCodeBlock sym archFns halloc hmap g regStruct = do
  let regAssign = crucGenRegAssignment archFns
  let crucRegTypes = typeCtxToCrucible (fmapFC M.typeRepr regAssign)
  let macawStructRepr = C.StructRepr crucRegTypes
  -- Run the symbolic simulator.
  cfg <- C.initialConfig 0 []
  let ptrWidth :: M.AddrWidthRepr (M.ArchAddrWidth arch)
      ptrWidth = M.addrWidthRepr ptrWidth
  let ctx :: C.SimContext MacawSimulatorState sym MacawExt
      ctx = C.SimContext { C._ctxSymInterface = sym
                         , C.ctxSolverProof = \a -> a
                         , C.ctxIntrinsicTypes = MapF.empty
                         , C.simConfig = cfg
                         , C.simHandleAllocator = halloc
                         , C.printHandle = stdout
                         , C.extensionImpl = undefined
                         , C._functionBindings =
                              C.insertHandleMap (C.cfgHandle g) (C.UseCFG g (C.postdomInfo g)) $
                                createHandleMap ptrWidth hmap
                         , C._cruciblePersonality = MacawSimulatorState
                         }
  -- Create the symbolic simulator state
  let s = C.initSimState ctx C.emptyGlobals C.defaultErrorHandler
  C.runOverrideSim s macawStructRepr $ do
    let args :: C.RegMap sym (MacawFunctionArgs arch)
        args = C.RegMap (Ctx.singleton (C.RegEntry macawStructRepr regStruct))
    C.regValue <$> C.callCFG g args

-- | Run the simulator over a contiguous set of code.
runBlocks :: forall sym arch ids
           .  (IsSymInterface sym, M.ArchConstraints arch)
           => sym
           -> CrucGenArchFunctions arch
              -- ^ Crucible specific functions.
           -> M.Memory (M.ArchAddrWidth arch)
              -- ^ Memory image for executable
           -> C.FunctionName
              -- ^ Name of function for pretty print purposes.
           -> (M.ArchAddrWord arch -> C.Position)
              -- ^ Function that maps offsets from start of block to Crucible position.
           -> [M.Block arch ids]
              -- ^ List of blocks for this region.
           -> Ctx.Assignment (C.RegValue' sym) (CtxToCrucibleType (ArchRegContext arch))
              -- ^ Register assignment
           -> IO (C.ExecResult
                   MacawSimulatorState
                   sym
                   MacawExt
                   (C.RegEntry sym (C.StructType (CtxToCrucibleType (ArchRegContext arch)))))
runBlocks sym archFns mem nm posFn macawBlocks regStruct = do
  halloc <- C.newHandleAllocator
  memBaseVarMap <- stToIO $ mkMemBaseVarMap halloc mem
  (hmap, C.SomeCFG g) <- stToIO $ mkBlocksCFG halloc archFns memBaseVarMap nm posFn macawBlocks
  -- Run the symbolic simulator.
  runCodeBlock sym archFns halloc hmap g regStruct
