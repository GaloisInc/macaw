{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Main (main) where

import           Control.Lens ( (^.) )
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ElfEdit as Elf
import qualified Data.Foldable as F
import qualified Data.Map as Map
import           Data.Maybe ( mapMaybe )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Sequence as Seq
import qualified Prettyprinter as PP
import           System.FilePath ( (</>), (<.>) )
import qualified System.FilePath.Glob as SFG
import qualified System.IO as IO
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import qualified Test.Tasty.Options as TTO
import qualified Test.Tasty.Runners as TTR

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as M
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Testing as MST
import qualified Data.Macaw.X86 as MX
import           Data.Macaw.X86.Symbolic ()
import qualified Data.Macaw.X86.Symbolic as MXS
import qualified Data.Macaw.X86.Symbolic.ABI.SysV as SysV
import qualified What4.Config as WC
import qualified What4.Interface as WI
import qualified What4.ProblemFeatures as WPF
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.LLVM.MemModel as LLVM

import qualified What4.FloatMode as W4
import qualified What4.Expr.Builder as W4
import qualified Data.Parameterized.Context as Ctx
import qualified What4.Protocol.Online as WPO
import qualified Lang.Crucible.CFG.Extension as CCE

-- | A Tasty option to tell us to save SMT queries and responses to /tmp for debugging purposes
data SaveSMT = SaveSMT Bool
  deriving (Eq, Show)

instance TTO.IsOption SaveSMT where
  defaultValue = SaveSMT False
  parseValue v = SaveSMT <$> TTO.safeReadBool v
  optionName = pure "save-smt"
  optionHelp = pure "Save SMT sessions to files in /tmp for debugging"

-- | A tasty option to have the test suite save the macaw IR for each test case to /tmp for debugging purposes
data SaveMacaw = SaveMacaw Bool

instance TTO.IsOption SaveMacaw where
  defaultValue = SaveMacaw False
  parseValue v = SaveMacaw <$> TTO.safeReadBool v
  optionName = pure "save-macaw"
  optionHelp = pure "Save Macaw IR for each test case to /tmp for debugging"

ingredients :: [TTR.Ingredient]
ingredients = TT.includingOptions [ TTO.Option (Proxy @SaveSMT)
                                  , TTO.Option (Proxy @SaveMacaw)
                                  ] : TT.defaultIngredients

getRegName ::
  Ctx.Index (MS.MacawCrucibleRegTypes MX.X86_64) t ->
  String
getRegName reg =
  case Ctx.intIndex (Ctx.indexVal reg) (Ctx.size MXS.x86RegAssignment) of
    Just (Some i) ->
      let r = MXS.x86RegAssignment Ctx.! i
          rName = MS.crucGenArchRegName MXS.x86_64MacawSymbolicFns r
      in show rName
    Nothing -> error "impossible"

main :: IO ()
main = do
  -- These are pass/fail in that the assertions in the "pass" set are true (and
  -- the solver returns Unsat), while the assertions in the "fail" set are false
  -- (and the solver returns Sat).
  passTestFilePaths <- SFG.glob "tests/pass/**/*.exe"
  failTestFilePaths <- SFG.glob "tests/fail/**/*.exe"
  let passRes = MST.SimulationResult MST.Unsat
  let failRes = MST.SimulationResult MST.Sat
  let passTests mmPreset = TT.testGroup "True assertions" (map (mkSymExTest passRes mmPreset) passTestFilePaths)
  let failTests mmPreset = TT.testGroup "False assertions" (map (mkSymExTest failRes mmPreset) failTestFilePaths)
  TT.defaultMainWithIngredients ingredients $
    TT.testGroup "macaw-x86-symbolic tests"
      [ TT.testGroup "Unit tests" 
          [ TTH.testCase "ip" $ getRegName MXS.rip TTH.@?= "r!ip"
          , TTH.testCase "rax" $ getRegName MXS.rax TTH.@?= "r!rax"
          , TTH.testCase "rbx" $ getRegName MXS.rbx TTH.@?= "r!rbx"
          , TTH.testCase "rcx" $ getRegName MXS.rcx TTH.@?= "r!rcx"
          , TTH.testCase "rdx" $ getRegName MXS.rdx TTH.@?= "r!rdx"
          , TTH.testCase "rsp" $ getRegName MXS.rsp TTH.@?= "r!rsp"
          , TTH.testCase "rbp" $ getRegName MXS.rbp TTH.@?= "r!rbp"
          , TTH.testCase "rsi" $ getRegName MXS.rsi TTH.@?= "r!rsi"
          , TTH.testCase "rdi" $ getRegName MXS.rdi TTH.@?= "r!rdi"
          , TTH.testCase "r8" $ getRegName MXS.r8 TTH.@?= "r!r8"
          , TTH.testCase "r9" $ getRegName MXS.r9 TTH.@?= "r!r9"
          , TTH.testCase "r10" $ getRegName MXS.r10 TTH.@?= "r!r10"
          , TTH.testCase "r11" $ getRegName MXS.r11 TTH.@?= "r!r11"
          , TTH.testCase "r12" $ getRegName MXS.r12 TTH.@?= "r!r12"
          , TTH.testCase "r13" $ getRegName MXS.r13 TTH.@?= "r!r13"
          , TTH.testCase "r14" $ getRegName MXS.r14 TTH.@?= "r!r14"
          , TTH.testCase "r15" $ getRegName MXS.r15 TTH.@?= "r!r15"
          ]
      , TT.testGroup "Binary tests" $
          map (\mmPreset ->
                TT.testGroup (MST.describeMemModelPreset mmPreset)
                             [passTests mmPreset, failTests mmPreset])
              [MST.DefaultMemModel, MST.LazyMemModel]
      ]

hasTestPrefix :: Some (M.DiscoveryFunInfo arch) -> Maybe (BS8.ByteString, Some (M.DiscoveryFunInfo arch))
hasTestPrefix (Some dfi) = do
  bsname <- M.discoveredFunSymbol dfi
  if BS8.pack "test_" `BS8.isPrefixOf` bsname
    then return (bsname, Some dfi)
    else Nothing

-- | X86_64 functions with a single scalar return value return it in %rax
--
-- Since all test functions must return a value to assert as true, this is
-- straightforward to extract
x86ResultExtractor :: (CB.IsSymInterface sym) => MS.ArchVals MX.X86_64 -> MST.ResultExtractor sym MX.X86_64
x86ResultExtractor archVals = MST.ResultExtractor $ \regs _mem k -> do
  let re = MS.lookupReg archVals regs MX.RAX
  k PC.knownRepr (CS.regValue re)

data MacawX86SymbolicTest t = MacawX86SymbolicTest

setupRegsAndMem ::
  ( ext ~ MS.MacawExt MX.X86_64
  , CCE.IsSyntaxExtension ext
  , CB.IsSymBackend sym bak
  , LLVM.HasLLVMAnn sym
  , sym ~ W4.ExprBuilder scope st fs
  , bak ~ CBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , ?memOpts :: LLVM.MemOptions
  , MS.HasMacawLazySimulatorState p sym 64
  ) =>
  bak ->
  MS.GenArchVals MS.LLVMMemory MX.X86_64 ->
  MST.MemModelPreset ->
  MST.BinariesInfo MX.X86_64 ->
  IO ( CS.RegEntry sym (MS.ArchRegStruct MX.X86_64)
     , MST.InitialMem p sym MX.X86_64
     )
setupRegsAndMem bak archVals mmPreset binariesInfo = do
  let sym = CB.backendGetSym bak
  MST.InitialMem initMem mmConf <-
    case mmPreset of
      MST.DefaultMemModel -> MST.initialMem binariesInfo bak MX.x86_64_linux_info archVals
      MST.LazyMemModel -> MST.lazyInitialMem binariesInfo bak MX.x86_64_linux_info archVals

  let symArchFns = MS.archFunctions archVals
  initRegs <- MST.freshRegs symArchFns sym
  let kib = 1024
  let mib = 1024 * kib
  stackSize <- WI.bvLit sym CT.knownNat (BVS.mkBV CT.knownNat mib)
  (regs, mem) <- SysV.allocStack bak initMem initRegs stackSize
  retAddr <- SysV.freshRetAddr sym
  let spilled = SysV.SpilledArgs Seq.Empty
  (regs', mem') <- SysV.pushStackFrame bak mem regs spilled retAddr
  let crucRegTypes = MS.crucArchRegTypes symArchFns
  let regsEntry = CS.RegEntry (CT.StructRepr crucRegTypes) regs'
  let iMem = MST.InitialMem mem' mmConf
  pure (regsEntry, iMem)


mkSymExTest :: MST.SimulationResult -> MST.MemModelPreset -> FilePath -> TT.TestTree
mkSymExTest expected mmPreset exePath = TT.askOption $ \saveSMT@(SaveSMT _) -> TT.askOption $ \saveMacaw@(SaveMacaw _) -> TTH.testCaseSteps exePath $ \step -> do
  bytes <- BS.readFile exePath
  case Elf.decodeElfHeaderInfo bytes of
    Left (_, msg) -> TTH.assertFailure ("Error parsing ELF header from file '" ++ show exePath ++ "': " ++ msg)
    Right (Elf.SomeElf ehi) -> do
      case Elf.headerClass (Elf.header ehi) of
        Elf.ELFCLASS32 -> TTH.assertFailure "32 bit x86 binaries are not supported"
        Elf.ELFCLASS64 -> do
          binariesInfo <- MST.runDiscovery ehi exePath MST.toAddrSymMap MX.x86_64_linux_info MX.x86_64PLTStubInfo
          let funInfos = Map.elems (MST.binaryDiscState (MST.mainBinaryInfo binariesInfo) ^. M.funInfo)
          let testEntryPoints = mapMaybe hasTestPrefix funInfos
          F.forM_ testEntryPoints $ \(name, Some dfi) -> do
            step ("Testing " ++ BS8.unpack name)
            writeMacawIR saveMacaw (BS8.unpack name) dfi
            Some (gen :: PN.NonceGenerator IO t) <- PN.newIONonceGenerator
            sym <- W4.newExprBuilder W4.FloatRealRepr MacawX86SymbolicTest gen
            CBO.withYicesOnlineBackend sym CBO.NoUnsatFeatures WPF.noFeatures $ \bak -> do
              -- We are using the z3 backend to discharge proof obligations, so
              -- we need to add its options to the backend configuration
              let solver = WS.z3Adapter
              let backendConf = WI.getConfiguration sym
              WC.extendConfig (WS.solver_adapter_config_options solver) backendConf

              execFeatures <- MST.defaultExecFeatures (MST.SomeOnlineBackend bak)
              archVals <- case MS.archVals (Proxy @MX.X86_64) Nothing of
                            Just archVals -> pure archVals
                            Nothing -> error "mkSymExTest: impossible"
              let extract = x86ResultExtractor archVals
              logger <- makeGoalLogger saveSMT solver name exePath
              let ?memOpts = LLVM.defaultMemOptions

              MS.withArchConstraints archVals $ do
                halloc <- CFH.newHandleAllocator
                let ?recordLLVMAnnotation = \_ _ _ -> return ()

                (regs, iMem) <- setupRegsAndMem bak archVals mmPreset binariesInfo
                (memVar, execResult) <-
                  MST.simDiscoveredFunction bak execFeatures archVals halloc iMem regs binariesInfo dfi

                simRes <- MST.summarizeExecution solver logger bak memVar extract execResult
                TTH.assertEqual "AssertionResult" expected simRes

writeMacawIR :: (MC.ArchConstraints arch) => SaveMacaw -> String -> M.DiscoveryFunInfo arch ids -> IO ()
writeMacawIR (SaveMacaw sm) name dfi
  | not sm = return ()
  | otherwise = writeFile (toSavedMacawPath name) (show (PP.pretty dfi))

toSavedMacawPath :: String -> FilePath
toSavedMacawPath testName = "/tmp" </> name <.> "macaw"
  where
    name = fmap escapeSlash testName

-- | Construct a solver logger that saves the SMT session for the goal solving
-- in /tmp (if requested by the save-smt option)
--
-- The adapter name is included so that, if the same test is solved with
-- multiple solvers, we can differentiate them.
makeGoalLogger :: SaveSMT -> WS.SolverAdapter st -> BS8.ByteString -> FilePath -> IO WS.LogData
makeGoalLogger (SaveSMT saveSMT) adapter funName p
  | not saveSMT = return WS.defaultLogData
  | otherwise = do
      hdl <- IO.openFile (toSavedSMTSessionPath adapter funName p) IO.WriteMode
      return (WS.defaultLogData { WS.logHandle = Just hdl })


-- | Construct a path in /tmp to save the SMT session to
--
-- Just take the original path name and turn all of the slashes into underscores to escape them
toSavedSMTSessionPath :: WS.SolverAdapter st -> BS8.ByteString -> FilePath -> FilePath
toSavedSMTSessionPath adapter funName p = "/tmp" </> filename <.> "smtlib2"
  where
    filename = concat [ fmap escapeSlash p
                      , "_"
                      , BS8.unpack funName
                      , "_"
                      , WS.solver_adapter_name adapter
                      ]

escapeSlash :: Char -> Char
escapeSlash '/' = '_'
escapeSlash c = c
