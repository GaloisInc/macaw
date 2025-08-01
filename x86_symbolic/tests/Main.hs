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
import qualified Data.Parameterized.Context as Ctx
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
import qualified Data.Macaw.Symbolic.Memory as MSM (defaultProcessMacawAssertion, MacawProcessAssertion)
import qualified Data.Macaw.Symbolic.Testing as MST
import qualified Data.Macaw.X86 as MX
import           Data.Macaw.X86.Symbolic ()
import qualified Data.Macaw.X86.Symbolic as MXS
import qualified Data.Macaw.X86.Symbolic.Regs as MXSR
import qualified Data.Macaw.X86.Symbolic.ABI.SysV as SysV
import qualified What4.Config as WC
import qualified What4.Expr.Builder as W4
import qualified What4.Interface as WI
import qualified What4.ProblemFeatures as WPF
import qualified What4.Protocol.Online as WPO
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.CFG.Extension as CCE
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.LLVM.MemModel as LLVM

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
          [ TTH.testCase "ip" $ getRegName MXSR.rip TTH.@?= "r!ip"
          , TTH.testCase "rax" $ getRegName MXSR.rax TTH.@?= "r!rax"
          , TTH.testCase "rbx" $ getRegName MXSR.rbx TTH.@?= "r!rbx"
          , TTH.testCase "rcx" $ getRegName MXSR.rcx TTH.@?= "r!rcx"
          , TTH.testCase "rdx" $ getRegName MXSR.rdx TTH.@?= "r!rdx"
          , TTH.testCase "rsp" $ getRegName MXSR.rsp TTH.@?= "r!rsp"
          , TTH.testCase "rbp" $ getRegName MXSR.rbp TTH.@?= "r!rbp"
          , TTH.testCase "rsi" $ getRegName MXSR.rsi TTH.@?= "r!rsi"
          , TTH.testCase "rdi" $ getRegName MXSR.rdi TTH.@?= "r!rdi"
          , TTH.testCase "r8" $ getRegName MXSR.r8 TTH.@?= "r!r8"
          , TTH.testCase "r9" $ getRegName MXSR.r9 TTH.@?= "r!r9"
          , TTH.testCase "r10" $ getRegName MXSR.r10 TTH.@?= "r!r10"
          , TTH.testCase "r11" $ getRegName MXSR.r11 TTH.@?= "r!r11"
          , TTH.testCase "r12" $ getRegName MXSR.r12 TTH.@?= "r!r12"
          , TTH.testCase "r13" $ getRegName MXSR.r13 TTH.@?= "r!r13"
          , TTH.testCase "r14" $ getRegName MXSR.r14 TTH.@?= "r!r14"
          , TTH.testCase "r15" $ getRegName MXSR.r15 TTH.@?= "r!r15"
          , TTH.testCase "cf" $ getRegName MXSR.cf TTH.@?= "r!cf"
          , TTH.testCase "pf" $ getRegName MXSR.pf TTH.@?= "r!pf"
          , TTH.testCase "af" $ getRegName MXSR.af TTH.@?= "r!af"
          , TTH.testCase "zf" $ getRegName MXSR.zf TTH.@?= "r!zf"
          , TTH.testCase "sf" $ getRegName MXSR.sf TTH.@?= "r!sf"
          , TTH.testCase "tf" $ getRegName MXSR.tf TTH.@?= "r!tf"
          , TTH.testCase "if" $ getRegName MXSR.if_ TTH.@?= "r!if"
          , TTH.testCase "df" $ getRegName MXSR.df TTH.@?= "r!df"
          , TTH.testCase "of" $ getRegName MXSR.of_ TTH.@?= "r!of"
          , TTH.testCase "ie" $ getRegName MXSR.ie TTH.@?= "r!ie"
          , TTH.testCase "de" $ getRegName MXSR.de TTH.@?= "r!de"
          , TTH.testCase "ze" $ getRegName MXSR.ze TTH.@?= "r!ze"
          , TTH.testCase "oe" $ getRegName MXSR.oe TTH.@?= "r!oe"
          , TTH.testCase "ue" $ getRegName MXSR.ue TTH.@?= "r!ue"
          , TTH.testCase "pe" $ getRegName MXSR.pe TTH.@?= "r!pe"
          , TTH.testCase "ef" $ getRegName MXSR.ef TTH.@?= "r!ef"
          , TTH.testCase "es" $ getRegName MXSR.es TTH.@?= "r!es"
          , TTH.testCase "c0" $ getRegName MXSR.c0 TTH.@?= "r!c0"
          , TTH.testCase "c1" $ getRegName MXSR.c1 TTH.@?= "r!c1"
          , TTH.testCase "c2" $ getRegName MXSR.c2 TTH.@?= "r!c2"
          , TTH.testCase "c3" $ getRegName MXSR.c3 TTH.@?= "r!c3"
          , TTH.testCase "top" $ getRegName MXSR.top TTH.@?= "r!x87Top"
          , TTH.testCase "tag0" $ getRegName MXSR.tag0 TTH.@?= "r!x87Tag0"
          , TTH.testCase "tag1" $ getRegName MXSR.tag1 TTH.@?= "r!x87Tag1"
          , TTH.testCase "tag2" $ getRegName MXSR.tag2 TTH.@?= "r!x87Tag2"
          , TTH.testCase "tag3" $ getRegName MXSR.tag3 TTH.@?= "r!x87Tag3"
          , TTH.testCase "tag4" $ getRegName MXSR.tag4 TTH.@?= "r!x87Tag4"
          , TTH.testCase "tag5" $ getRegName MXSR.tag5 TTH.@?= "r!x87Tag5"
          , TTH.testCase "tag6" $ getRegName MXSR.tag6 TTH.@?= "r!x87Tag6"
          , TTH.testCase "tag7" $ getRegName MXSR.tag7 TTH.@?= "r!x87Tag7"
          , TTH.testCase "st0" $ getRegName MXSR.st0 TTH.@?= "r!mm0"
          , TTH.testCase "st1" $ getRegName MXSR.st1 TTH.@?= "r!mm1"
          , TTH.testCase "st2" $ getRegName MXSR.st2 TTH.@?= "r!mm2"
          , TTH.testCase "st3" $ getRegName MXSR.st3 TTH.@?= "r!mm3"
          , TTH.testCase "st4" $ getRegName MXSR.st4 TTH.@?= "r!mm4"
          , TTH.testCase "st5" $ getRegName MXSR.st5 TTH.@?= "r!mm5"
          , TTH.testCase "st6" $ getRegName MXSR.st6 TTH.@?= "r!mm6"
          , TTH.testCase "st7" $ getRegName MXSR.st7 TTH.@?= "r!mm7"
          , TTH.testCase "mm0" $ getRegName MXSR.mm0 TTH.@?= "r!mm0"
          , TTH.testCase "mm1" $ getRegName MXSR.mm1 TTH.@?= "r!mm1"
          , TTH.testCase "mm2" $ getRegName MXSR.mm2 TTH.@?= "r!mm2"
          , TTH.testCase "mm3" $ getRegName MXSR.mm3 TTH.@?= "r!mm3"
          , TTH.testCase "mm4" $ getRegName MXSR.mm4 TTH.@?= "r!mm4"
          , TTH.testCase "mm5" $ getRegName MXSR.mm5 TTH.@?= "r!mm5"
          , TTH.testCase "mm6" $ getRegName MXSR.mm6 TTH.@?= "r!mm6"
          , TTH.testCase "mm7" $ getRegName MXSR.mm7 TTH.@?= "r!mm7"
          , TTH.testCase "zmm0" $ getRegName MXSR.zmm0 TTH.@?= "r!zmm0"
          , TTH.testCase "zmm1" $ getRegName MXSR.zmm1 TTH.@?= "r!zmm1"
          , TTH.testCase "zmm2" $ getRegName MXSR.zmm2 TTH.@?= "r!zmm2"
          , TTH.testCase "zmm3" $ getRegName MXSR.zmm3 TTH.@?= "r!zmm3"
          , TTH.testCase "zmm4" $ getRegName MXSR.zmm4 TTH.@?= "r!zmm4"
          , TTH.testCase "zmm5" $ getRegName MXSR.zmm5 TTH.@?= "r!zmm5"
          , TTH.testCase "zmm6" $ getRegName MXSR.zmm6 TTH.@?= "r!zmm6"
          , TTH.testCase "zmm7" $ getRegName MXSR.zmm7 TTH.@?= "r!zmm7"
          , TTH.testCase "zmm8" $ getRegName MXSR.zmm8 TTH.@?= "r!zmm8"
          , TTH.testCase "zmm9" $ getRegName MXSR.zmm9 TTH.@?= "r!zmm9"
          , TTH.testCase "zmm10" $ getRegName MXSR.zmm10 TTH.@?= "r!zmm10"
          , TTH.testCase "zmm11" $ getRegName MXSR.zmm11 TTH.@?= "r!zmm11"
          , TTH.testCase "zmm12" $ getRegName MXSR.zmm12 TTH.@?= "r!zmm12"
          , TTH.testCase "zmm13" $ getRegName MXSR.zmm13 TTH.@?= "r!zmm13"
          , TTH.testCase "zmm14" $ getRegName MXSR.zmm14 TTH.@?= "r!zmm14"
          , TTH.testCase "zmm15" $ getRegName MXSR.zmm15 TTH.@?= "r!zmm15"
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
  , MSM.MacawProcessAssertion sym
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
                let ?processMacawAssert = MSM.defaultProcessMacawAssertion

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
