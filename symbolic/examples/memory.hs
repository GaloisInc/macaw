{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

import           GHC.TypeLits
import           Control.Monad.ST ( stToIO, RealWorld )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Memory as MSM
import           Data.Proxy ( Proxy(..) )
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.LLVM.Intrinsics as CLI
import qualified Lang.Crucible.LLVM.DataLayout as LDL
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CSG
import qualified System.IO as IO
import qualified What4.Interface as WI

useCFG :: forall sym arch blocks
        . ( CB.IsSymInterface sym
          , MS.SymArchConstraints arch
          , 16 <= MC.ArchAddrWidth arch
          , Ord (WI.SymExpr sym WI.BaseNatType)
          , KnownNat (MC.ArchAddrWidth arch)
          )
       => CFH.HandleAllocator RealWorld
       -- ^ The handle allocator used to construct the CFG
       -> sym
       -- ^ The symbolic backend
       -> MS.ArchVals arch
       -- ^ 'ArchVals' from a prior call to 'archVals'
       -> CS.RegMap sym (MS.MacawFunctionArgs arch)
       -- ^ Initial register state for the simulation
       -> MC.Memory (MC.ArchAddrWidth arch)
       -- ^ The memory recovered by macaw
       -> MS.LookupFunctionHandle sym arch
       -- ^ A translator for machine code addresses to function handles
       -> CC.CFG (MS.MacawExt arch) blocks (MS.MacawFunctionArgs arch) (MS.MacawFunctionResult arch)
       -- ^ The CFG to simulate
       -> IO ()
useCFG hdlAlloc sym MS.ArchVals { MS.withArchEval = withArchEval }
       initialRegs mem lfh cfg = withArchEval sym $ \archEvalFns -> do
  let rep = CFH.handleReturnType (CC.cfgHandle cfg)
  memModelVar <- stToIO (CLM.mkMemVar hdlAlloc)
  (initialMem, memPtrTbl) <- MSM.newGlobalMemory (Proxy @arch) sym LDL.LittleEndian MSM.SymbolicMutable mem
  let extImpl = MS.macawExtensions archEvalFns memModelVar (MSM.mapRegionPointers memPtrTbl) lfh
  let simCtx = CS.initSimContext sym CLI.llvmIntrinsicTypes hdlAlloc IO.stderr CFH.emptyHandleMap extImpl MS.MacawSimulatorState
  let simGlobalState = CSG.insertGlobal memModelVar initialMem CS.emptyGlobals
  let simulation = CS.regValue <$> CS.callCFG cfg initialRegs
  let initialState = CS.InitialState simCtx simGlobalState CS.defaultAbortHandler (CS.runOverrideSim rep simulation)
  let executionFeatures = []
  execRes <- CS.executeCrucible executionFeatures initialState
  case execRes of
    CS.FinishedResult {} -> return ()
    _ -> putStrLn "Simulation failed"

main :: IO ()
main = return ()
