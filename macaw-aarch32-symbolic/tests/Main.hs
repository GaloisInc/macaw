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

import qualified Language.ASL.Globals as ASL
import qualified Data.Macaw.Architecture.Info as MAI

import qualified Data.Macaw.AArch32.Symbolic as MAS
import qualified Data.Macaw.AArch32.Symbolic.ABI as ABI
import qualified Data.Macaw.AArch32.Symbolic.Regs as MASR
import qualified Data.Macaw.ARM as MA
import qualified Data.Macaw.ARM.ARMReg as MAR
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as M
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Testing as MST
import qualified What4.Config as WC
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.ProblemFeatures as WPF
import qualified What4.Protocol.Online as WPO
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.LLVM.MemModel as LLVM
import qualified Lang.Crucible.CFG.Extension as CCE
import qualified Lang.Crucible.Types as CT

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
  Ctx.Index (MS.MacawCrucibleRegTypes MA.ARM) t ->
  String
getRegName reg =
  case Ctx.intIndex (Ctx.indexVal reg) (Ctx.size regs) of
    Just (Some i) ->
      let r = regs Ctx.! i
          rName = MS.crucGenArchRegName MAS.aarch32MacawSymbolicFns r
      in show rName
    Nothing -> error "impossible"
  where regs = MS.crucGenRegAssignment MAS.aarch32MacawSymbolicFns

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
    TT.testGroup "macaw-aarch32-symbolic tests"
    [ TT.testGroup "Unit tests" 
        [ TTH.testCase "r0" $ getRegName MASR.r0 TTH.@?= "zenc!rznzuR0"
        , TTH.testCase "r1" $ getRegName MASR.r1 TTH.@?= "zenc!rznzuR1"
        , TTH.testCase "r2" $ getRegName MASR.r2 TTH.@?= "zenc!rznzuR2"
        , TTH.testCase "r3" $ getRegName MASR.r3 TTH.@?= "zenc!rznzuR3"
        , TTH.testCase "r4" $ getRegName MASR.r4 TTH.@?= "zenc!rznzuR4"
        , TTH.testCase "r5" $ getRegName MASR.r5 TTH.@?= "zenc!rznzuR5"
        , TTH.testCase "r6" $ getRegName MASR.r6 TTH.@?= "zenc!rznzuR6"
        , TTH.testCase "r7" $ getRegName MASR.r7 TTH.@?= "zenc!rznzuR7"
        , TTH.testCase "r8" $ getRegName MASR.r8 TTH.@?= "zenc!rznzuR8"
        , TTH.testCase "r9" $ getRegName MASR.r9 TTH.@?= "zenc!rznzuR9"
        , TTH.testCase "r10" $ getRegName MASR.r10 TTH.@?= "zenc!rznzuR10"
        , TTH.testCase "r11" $ getRegName MASR.r11 TTH.@?= "zenc!rznzuR11"
        , TTH.testCase "fp" $ getRegName MASR.fp TTH.@?= "zenc!rznzuR11"
        , TTH.testCase "r12" $ getRegName MASR.r12 TTH.@?= "zenc!rznzuR12"
        , TTH.testCase "ip" $ getRegName MASR.ip TTH.@?= "zenc!rznzuR12"
        , TTH.testCase "r13" $ getRegName MASR.r13 TTH.@?= "zenc!rznzuR13"
        , TTH.testCase "sp" $ getRegName MASR.sp TTH.@?= "zenc!rznzuR13"
        , TTH.testCase "r14" $ getRegName MASR.r14 TTH.@?= "zenc!rznzuR14"
        , TTH.testCase "lr" $ getRegName MASR.lr TTH.@?= "zenc!rznzuR14"
        , TTH.testCase "v0" $ getRegName MASR.v0 TTH.@?= "zenc!rznzuV0"
        , TTH.testCase "v1" $ getRegName MASR.v1 TTH.@?= "zenc!rznzuV1"
        , TTH.testCase "v2" $ getRegName MASR.v2 TTH.@?= "zenc!rznzuV2"
        , TTH.testCase "v3" $ getRegName MASR.v3 TTH.@?= "zenc!rznzuV3"
        , TTH.testCase "v4" $ getRegName MASR.v4 TTH.@?= "zenc!rznzuV4"
        , TTH.testCase "v5" $ getRegName MASR.v5 TTH.@?= "zenc!rznzuV5"
        , TTH.testCase "v6" $ getRegName MASR.v6 TTH.@?= "zenc!rznzuV6"
        , TTH.testCase "v7" $ getRegName MASR.v7 TTH.@?= "zenc!rznzuV7"
        , TTH.testCase "v8" $ getRegName MASR.v8 TTH.@?= "zenc!rznzuV8"
        , TTH.testCase "v9" $ getRegName MASR.v9 TTH.@?= "zenc!rznzuV9"
        , TTH.testCase "v10" $ getRegName MASR.v10 TTH.@?= "zenc!rznzuV10"
        , TTH.testCase "v11" $ getRegName MASR.v11 TTH.@?= "zenc!rznzuV11"
        , TTH.testCase "v12" $ getRegName MASR.v12 TTH.@?= "zenc!rznzuV12"
        , TTH.testCase "v13" $ getRegName MASR.v13 TTH.@?= "zenc!rznzuV13"
        , TTH.testCase "v14" $ getRegName MASR.v14 TTH.@?= "zenc!rznzuV14"
        , TTH.testCase "v15" $ getRegName MASR.v15 TTH.@?= "zenc!rznzuV15"
        , TTH.testCase "v16" $ getRegName MASR.v16 TTH.@?= "zenc!rznzuV16"
        , TTH.testCase "v17" $ getRegName MASR.v17 TTH.@?= "zenc!rznzuV17"
        , TTH.testCase "v18" $ getRegName MASR.v18 TTH.@?= "zenc!rznzuV18"
        , TTH.testCase "v19" $ getRegName MASR.v19 TTH.@?= "zenc!rznzuV19"
        , TTH.testCase "v20" $ getRegName MASR.v20 TTH.@?= "zenc!rznzuV20"
        , TTH.testCase "v21" $ getRegName MASR.v21 TTH.@?= "zenc!rznzuV21"
        , TTH.testCase "v22" $ getRegName MASR.v22 TTH.@?= "zenc!rznzuV22"
        , TTH.testCase "v23" $ getRegName MASR.v23 TTH.@?= "zenc!rznzuV23"
        , TTH.testCase "v24" $ getRegName MASR.v24 TTH.@?= "zenc!rznzuV24"
        , TTH.testCase "v25" $ getRegName MASR.v25 TTH.@?= "zenc!rznzuV25"
        , TTH.testCase "v26" $ getRegName MASR.v26 TTH.@?= "zenc!rznzuV26"
        , TTH.testCase "v27" $ getRegName MASR.v27 TTH.@?= "zenc!rznzuV27"
        , TTH.testCase "v28" $ getRegName MASR.v28 TTH.@?= "zenc!rznzuV28"
        , TTH.testCase "v29" $ getRegName MASR.v29 TTH.@?= "zenc!rznzuV29"
        , TTH.testCase "v30" $ getRegName MASR.v30 TTH.@?= "zenc!rznzuV30"
        , TTH.testCase "v31" $ getRegName MASR.v31 TTH.@?= "zenc!rznzuV31"
        ]
    , TT.testGroup "Binary Tests" $
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

-- | ARM functions with a single scalar return value return it in %r0
--
-- Since all test functions must return a value to assert as true, this is
-- straightforward to extract
armResultExtractor :: ( CB.IsSymInterface sym
                      )
                   => MS.ArchVals MA.ARM
                   -> MST.ResultExtractor sym MA.ARM
armResultExtractor archVals = MST.ResultExtractor $ \regs _mem k -> do
  let re = MS.lookupReg archVals regs MAR.r0
  k PC.knownRepr (CS.regValue re)

setupRegsAndMem ::
  ( ext ~ MS.MacawExt MA.ARM
  , CCE.IsSyntaxExtension ext
  , CB.IsSymBackend sym bak
  , LLVM.HasLLVMAnn sym
  , sym ~ WEB.ExprBuilder scope st fs
  , bak ~ CBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , ?memOpts :: LLVM.MemOptions
  , MS.HasMacawLazySimulatorState p sym 32
  ) =>
  bak ->
  MS.GenArchVals MS.LLVMMemory MA.ARM ->
  MST.MemModelPreset ->
  MST.BinariesInfo MA.ARM ->
  IO ( CS.RegEntry sym (MS.ArchRegStruct MA.ARM)
     , MST.InitialMem p sym MA.ARM
     )
setupRegsAndMem bak archVals mmPreset binariesInfo = do
  let sym = CB.backendGetSym bak
  MST.InitialMem initMem mmConf <-
    case mmPreset of
      MST.DefaultMemModel -> MST.initialMem binariesInfo bak MA.arm_linux_info archVals
      MST.LazyMemModel -> MST.lazyInitialMem binariesInfo bak MA.arm_linux_info archVals

  let symArchFns = MS.archFunctions archVals
  initRegs <- MST.freshRegs symArchFns sym
  let kib = 1024
  let mib = 1024 * kib
  stackSize <- WI.bvLit sym CT.knownNat (BVS.mkBV CT.knownNat mib)
  (regs, mem) <- ABI.allocStack bak initMem initRegs stackSize
  let spilled = ABI.SpilledArgs Seq.Empty
  (regs', mem') <- ABI.pushStackFrame bak mem regs spilled
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
        Elf.ELFCLASS32 ->
          symExTestSized expected mmPreset exePath saveSMT saveMacaw step ehi MA.arm_linux_info
        Elf.ELFCLASS64 -> TTH.assertFailure "64 bit ARM is not supported"

data MacawAarch32TestData t = MacawAarch32TestData

symExTestSized :: MST.SimulationResult
               -> MST.MemModelPreset
               -> FilePath
               -> SaveSMT
               -> SaveMacaw
               -> (String -> IO ())
               -> Elf.ElfHeaderInfo 32
               -> MAI.ArchitectureInfo MA.ARM
               -> TTH.Assertion
symExTestSized expected mmPreset exePath saveSMT saveMacaw step ehi archInfo = do
   binfo <- MST.runDiscovery ehi exePath MST.toAddrSymMap archInfo MA.armPLTStubInfo
   let funInfos = Map.elems (MST.binaryDiscState (MST.mainBinaryInfo binfo) ^. M.funInfo)
   let testEntryPoints = mapMaybe hasTestPrefix funInfos
   F.forM_ testEntryPoints $ \(name, Some dfi) -> do
     step ("Testing " ++ BS8.unpack name ++ " at " ++ show (M.discoveredFunAddr dfi))
     writeMacawIR saveMacaw (BS8.unpack name) dfi
     Some (gen :: PN.NonceGenerator IO t) <- PN.newIONonceGenerator
     sym <- WEB.newExprBuilder WEB.FloatRealRepr MacawAarch32TestData gen
     CBO.withYicesOnlineBackend sym CBO.NoUnsatFeatures WPF.noFeatures $ \bak -> do
       -- We are using the z3 backend to discharge proof obligations, so
       -- we need to add its options to the backend configuration
       let solver = WS.z3Adapter
       let backendConf = WI.getConfiguration sym
       WC.extendConfig (WS.solver_adapter_config_options solver) backendConf

       execFeatures <- MST.defaultExecFeatures (MST.SomeOnlineBackend bak)
       archVals <- case MS.archVals (Proxy @MA.ARM) Nothing of
                     Just archVals -> pure archVals
                     Nothing -> error "symExTestSized: impossible"
       let extract = armResultExtractor archVals
       logger <- makeGoalLogger saveSMT solver name exePath
       let ?memOpts = LLVM.defaultMemOptions

       MS.withArchConstraints archVals $ do
         halloc <- CFH.newHandleAllocator
         let ?recordLLVMAnnotation = \_ _ _ -> return ()

         (regs, iMem) <- setupRegsAndMem bak archVals mmPreset binfo
         (memVar, execResult) <-
           MST.simDiscoveredFunction bak execFeatures archVals halloc iMem regs binfo dfi

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
