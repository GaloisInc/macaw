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
module Data.Macaw.Symbolic
  ( Data.Macaw.Symbolic.CrucGen.MacawSymbolicArchFunctions(..)
  , Data.Macaw.Symbolic.CrucGen.CrucGen
  , Data.Macaw.Symbolic.CrucGen.MemSegmentMap
  , MacawSimulatorState
  , freshVarsForRegs
  , runCodeBlock
  , runBlocks
  , mkBlocksCFG
  , mkFunCFG
  , Data.Macaw.Symbolic.PersistentState.ArchRegContext
  , Data.Macaw.Symbolic.PersistentState.ToCrucibleType
  , Data.Macaw.Symbolic.PersistentState.FromCrucibleType
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
  , toCrucAndBack
  ) where

import           Control.Lens ((^.))
import           Control.Monad (forM)
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

type FunBlockMap arch s = Map (M.ArchSegmentOff arch, Word64) (CR.Label s)

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
mkFunCFG archFns halloc memBaseVarMap nm posFn fn = do
  mkCrucCFG archFns halloc nm $ do
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
    let regReg = CR.Reg { CR.regPosition = posFn (M.discoveredFunAddr fn)
                        , CR.regId = 0
                        , CR.typeOfReg = C.StructRepr (crucArchRegTypes archFns)
                        }
    fmap concat $
      forM (Map.elems (fn^.M.parsedBlocks)) $ \b -> do
        -- TODO: Initialize value in regReg with initial registers
        addParsedBlock archFns memBaseVarMap blockLabelMap posFn regReg b

macawExecApp :: sym
             -> (forall utp . f utp -> IO (C.RegValue sym utp))
             -> MacawExprExtension arch f tp
             -> IO (C.RegValue sym tp)
macawExecApp sym f e0 =
  case e0 of
    MacawOverflows op x y c -> do
      xv <- f x
      yv <- f y
      cv <- f c
      case op of
        _ -> undefined sym xv yv cv


type EvalStmtFunc f p sym ext =
  forall rtp blocks r ctx tp'.
    f (C.RegEntry sym) tp'
    -> C.CrucibleState p sym ext rtp blocks r ctx
    -> IO (C.RegValue sym tp', C.CrucibleState p sym ext rtp blocks r ctx)

-- | Function for evaluating an architecture-specific statement
type MacawArchEvalFn sym arch =
  EvalStmtFunc (MacawArchStmtExtension arch) MacawSimulatorState sym (MacawExt arch)

macawExecStmt :: MacawArchEvalFn sym arch
              -> EvalStmtFunc (MacawStmtExtension arch) MacawSimulatorState sym (MacawExt arch)
macawExecStmt archStmtFn s0 st =
  case s0 of
    MacawReadMem{} -> undefined
    MacawCondReadMem{} -> undefined
    MacawWriteMem{} -> undefined
    MacawFreshSymbolic{} -> undefined
    MacawCall{} -> undefined
    MacawArchStmtExtension s -> archStmtFn s st

-- | Return macaw extension evaluation functions.
macawExtensions :: MacawArchEvalFn sym arch
                -> C.ExtensionImpl MacawSimulatorState sym (MacawExt arch)
macawExtensions f =
  C.ExtensionImpl { C.extensionEval = macawExecApp
                  , C.extensionExec = macawExecStmt f
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
           -> Ctx.Assignment (C.RegValue' sym) (CtxToCrucibleType (ArchRegContext arch))
              -- ^ Register assignment
           -> IO (C.ExecResult
                   MacawSimulatorState
                   sym
                   (MacawExt arch)
                   (C.RegEntry sym (C.StructType (CtxToCrucibleType (ArchRegContext arch)))))
runBlocks sym archFns archEval mem nm posFn macawBlocks regStruct = do
  halloc <- C.newHandleAllocator
  memBaseVarMap <- stToIO $ mkMemBaseVarMap halloc mem
  C.SomeCFG g <- stToIO $ mkBlocksCFG archFns halloc memBaseVarMap nm posFn macawBlocks
  -- Run the symbolic simulator.
  runCodeBlock sym archFns archEval halloc g regStruct
