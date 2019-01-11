{-# LANGUAGE FlexibleContexts #-}
import           Control.Monad.ST ( stToIO, RealWorld )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.LLVM.Intrinsics as CLI
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CSG
import qualified System.IO as IO

useCFG :: (CB.IsSymInterface sym, MS.SymArchConstraints arch)
       => CFH.HandleAllocator RealWorld
       -- ^ The handle allocator used to construct the CFG
       -> sym
       -- ^ The symbolic backend
       -> MS.ArchVals arch
       -- ^ 'ArchVals' from a prior call to 'archVals'
       -> CS.RegMap sym (MS.MacawFunctionArgs arch)
       -- ^ Initial register state for the simulation
       -> CLM.MemImpl sym
       -- ^ The initial memory state of the simulator
       -> MS.GlobalMap sym (MC.ArchAddrWidth arch)
       -- ^ A translator of machine code addresses to LLVM pointers
       -> MS.LookupFunctionHandle sym arch
       -- ^ A translator for machine code addresses to function handles
       -> CC.CFG (MS.MacawExt arch) blocks (MS.MacawFunctionArgs arch) (MS.MacawFunctionResult arch)
       -- ^ The CFG to simulate
       -> IO ()
useCFG hdlAlloc sym MS.ArchVals { MS.withArchEval = withArchEval }
       initialRegs initialMem globalMap lfh cfg = withArchEval sym $ \archEvalFns -> do
  let rep = CFH.handleReturnType (CC.cfgHandle cfg)
  memModelVar <- stToIO (CLM.mkMemVar hdlAlloc)
  let extImpl = MS.macawExtensions archEvalFns memModelVar globalMap lfh
  let simCtx = CS.initSimContext sym CLI.llvmIntrinsicTypes hdlAlloc IO.stderr CFH.emptyHandleMap extImpl MS.MacawSimulatorState
  let simGlobalState = CSG.insertGlobal memModelVar initialMem CS.emptyGlobals
  let simulation = CS.regValue <$> CS.callCFG cfg initialRegs
  let initialState = CS.InitialState simCtx simGlobalState CS.defaultAbortHandler (CS.runOverrideSim rep simulation)
  let executionFeatures = []
  execRes <- CS.executeCrucible executionFeatures initialState
  case execRes of
    CS.FinishedResult {} -> return ()
    _ -> putStrLn "Simulation failed"
