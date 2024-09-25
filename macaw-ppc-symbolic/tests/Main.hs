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
import           GHC.TypeNats ( KnownNat, type (<=) )
import qualified Prettyprinter as PP
import           System.FilePath ( (</>), (<.>) )
import qualified System.FilePath.Glob as SFG
import qualified System.IO as IO
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import qualified Test.Tasty.Options as TTO
import qualified Test.Tasty.Runners as TTR

import qualified Dismantle.PPC as DP
import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.BinaryLoader.PPC as MBLP
import qualified Data.Macaw.BinaryLoader.PPC.TOC as MBLP
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as M
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as MMEL
import qualified Data.Macaw.Memory.ElfLoader.PLTStubs as MMELP
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Testing as MST
import qualified Data.Macaw.PPC as MP
import qualified Data.Macaw.PPC.Symbolic as MPS
import qualified Data.Macaw.PPC.Symbolic.Regs as MPSR
import qualified SemMC.Architecture.PPC as SAP
import qualified What4.Config as WC
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.ProblemFeatures as WPF
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Simulator as CS
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
  Ctx.Index (MS.MacawCrucibleRegTypes MP.PPC32) t ->
  String
getRegName reg =
  case Ctx.intIndex (Ctx.indexVal reg) (Ctx.size regs) of
    Just (Some i) ->
      let r = regs Ctx.! i
          rName = MS.crucGenArchRegName MPS.ppcMacawSymbolicFns r
      in show rName
    Nothing -> error "impossible"
  where regs = MS.crucGenRegAssignment (MPS.ppcMacawSymbolicFns @MP.V32)

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
    TT.testGroup "macaw-ppc-symbolic tests"
    [ TT.testGroup "Unit tests" 
        [ TTH.testCase "ip" $ getRegName MPSR.ip TTH.@?= "r!ip"
        , TTH.testCase "lnk" $ getRegName MPSR.lnk TTH.@?= "r!lnk"
        , TTH.testCase "ctr" $ getRegName MPSR.ctr TTH.@?= "r!ctr"
        , TTH.testCase "xer" $ getRegName MPSR.xer TTH.@?= "r!xer"
        , TTH.testCase "cr" $ getRegName MPSR.cr TTH.@?= "r!cr"
        , TTH.testCase "fpscr" $ getRegName MPSR.fpscr TTH.@?= "r!fpscr"
        , TTH.testCase "vscr" $ getRegName MPSR.vscr TTH.@?= "r!vscr"
        , TTH.testCase "r0" $ getRegName MPSR.r0 TTH.@?= "r!r0"
        , TTH.testCase "r1" $ getRegName MPSR.r1 TTH.@?= "r!r1"
        , TTH.testCase "r2" $ getRegName MPSR.r2 TTH.@?= "r!r2"
        , TTH.testCase "r3" $ getRegName MPSR.r3 TTH.@?= "r!r3"
        , TTH.testCase "r4" $ getRegName MPSR.r4 TTH.@?= "r!r4"
        , TTH.testCase "r5" $ getRegName MPSR.r5 TTH.@?= "r!r5"
        , TTH.testCase "r6" $ getRegName MPSR.r6 TTH.@?= "r!r6"
        , TTH.testCase "r7" $ getRegName MPSR.r7 TTH.@?= "r!r7"
        , TTH.testCase "r8" $ getRegName MPSR.r8 TTH.@?= "r!r8"
        , TTH.testCase "r9" $ getRegName MPSR.r9 TTH.@?= "r!r9"
        , TTH.testCase "r10" $ getRegName MPSR.r10 TTH.@?= "r!r10"
        , TTH.testCase "r11" $ getRegName MPSR.r11 TTH.@?= "r!r11"
        , TTH.testCase "r12" $ getRegName MPSR.r12 TTH.@?= "r!r12"
        , TTH.testCase "r13" $ getRegName MPSR.r13 TTH.@?= "r!r13"
        , TTH.testCase "r14" $ getRegName MPSR.r14 TTH.@?= "r!r14"
        , TTH.testCase "r15" $ getRegName MPSR.r15 TTH.@?= "r!r15"
        , TTH.testCase "r16" $ getRegName MPSR.r16 TTH.@?= "r!r16"
        , TTH.testCase "r17" $ getRegName MPSR.r17 TTH.@?= "r!r17"
        , TTH.testCase "r18" $ getRegName MPSR.r18 TTH.@?= "r!r18"
        , TTH.testCase "r19" $ getRegName MPSR.r19 TTH.@?= "r!r19"
        , TTH.testCase "r20" $ getRegName MPSR.r20 TTH.@?= "r!r20"
        , TTH.testCase "r21" $ getRegName MPSR.r21 TTH.@?= "r!r21"
        , TTH.testCase "r22" $ getRegName MPSR.r22 TTH.@?= "r!r22"
        , TTH.testCase "r23" $ getRegName MPSR.r23 TTH.@?= "r!r23"
        , TTH.testCase "r24" $ getRegName MPSR.r24 TTH.@?= "r!r24"
        , TTH.testCase "r25" $ getRegName MPSR.r25 TTH.@?= "r!r25"
        , TTH.testCase "r26" $ getRegName MPSR.r26 TTH.@?= "r!r26"
        , TTH.testCase "r27" $ getRegName MPSR.r27 TTH.@?= "r!r27"
        , TTH.testCase "r28" $ getRegName MPSR.r28 TTH.@?= "r!r28"
        , TTH.testCase "r29" $ getRegName MPSR.r29 TTH.@?= "r!r29"
        , TTH.testCase "r30" $ getRegName MPSR.r30 TTH.@?= "r!r30"
        , TTH.testCase "r31" $ getRegName MPSR.r31 TTH.@?= "r!r31"
        , TTH.testCase "f0" $ getRegName MPSR.f0 TTH.@?= "r!f0"
        , TTH.testCase "f1" $ getRegName MPSR.f1 TTH.@?= "r!f1"
        , TTH.testCase "f2" $ getRegName MPSR.f2 TTH.@?= "r!f2"
        , TTH.testCase "f3" $ getRegName MPSR.f3 TTH.@?= "r!f3"
        , TTH.testCase "f4" $ getRegName MPSR.f4 TTH.@?= "r!f4"
        , TTH.testCase "f5" $ getRegName MPSR.f5 TTH.@?= "r!f5"
        , TTH.testCase "f6" $ getRegName MPSR.f6 TTH.@?= "r!f6"
        , TTH.testCase "f7" $ getRegName MPSR.f7 TTH.@?= "r!f7"
        , TTH.testCase "f8" $ getRegName MPSR.f8 TTH.@?= "r!f8"
        , TTH.testCase "f9" $ getRegName MPSR.f9 TTH.@?= "r!f9"
        , TTH.testCase "f10" $ getRegName MPSR.f10 TTH.@?= "r!f10"
        , TTH.testCase "f11" $ getRegName MPSR.f11 TTH.@?= "r!f11"
        , TTH.testCase "f12" $ getRegName MPSR.f12 TTH.@?= "r!f12"
        , TTH.testCase "f13" $ getRegName MPSR.f13 TTH.@?= "r!f13"
        , TTH.testCase "f14" $ getRegName MPSR.f14 TTH.@?= "r!f14"
        , TTH.testCase "f15" $ getRegName MPSR.f15 TTH.@?= "r!f15"
        , TTH.testCase "f16" $ getRegName MPSR.f16 TTH.@?= "r!f16"
        , TTH.testCase "f17" $ getRegName MPSR.f17 TTH.@?= "r!f17"
        , TTH.testCase "f18" $ getRegName MPSR.f18 TTH.@?= "r!f18"
        , TTH.testCase "f19" $ getRegName MPSR.f19 TTH.@?= "r!f19"
        , TTH.testCase "f20" $ getRegName MPSR.f20 TTH.@?= "r!f20"
        , TTH.testCase "f21" $ getRegName MPSR.f21 TTH.@?= "r!f21"
        , TTH.testCase "f22" $ getRegName MPSR.f22 TTH.@?= "r!f22"
        , TTH.testCase "f23" $ getRegName MPSR.f23 TTH.@?= "r!f23"
        , TTH.testCase "f24" $ getRegName MPSR.f24 TTH.@?= "r!f24"
        , TTH.testCase "f25" $ getRegName MPSR.f25 TTH.@?= "r!f25"
        , TTH.testCase "f26" $ getRegName MPSR.f26 TTH.@?= "r!f26"
        , TTH.testCase "f27" $ getRegName MPSR.f27 TTH.@?= "r!f27"
        , TTH.testCase "f28" $ getRegName MPSR.f28 TTH.@?= "r!f28"
        , TTH.testCase "f29" $ getRegName MPSR.f29 TTH.@?= "r!f29"
        , TTH.testCase "f30" $ getRegName MPSR.f30 TTH.@?= "r!f30"
        , TTH.testCase "f31" $ getRegName MPSR.f31 TTH.@?= "r!f31"
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

-- | PowerPC functions (at least in the common ABIs) with a single scalar return value return it in %r3
--
-- Since all test functions must return a value to assert as true, this is
-- straightforward to extract
ppcResultExtractor :: ( arch ~ MP.AnyPPC v
                      , CB.IsSymInterface sym
                      , MP.KnownVariant v
                      , MM.MemWidth (SAP.AddrWidth v)
                      , MC.ArchConstraints arch
                      , MS.ArchInfo arch
                      , KnownNat (SAP.AddrWidth v)
                      )
                   => MS.ArchVals arch
                   -> MST.ResultExtractor sym arch
ppcResultExtractor archVals = MST.ResultExtractor $ \regs _mem k -> do
  let re = MS.lookupReg archVals regs (MP.PPC_GP (DP.GPR 3))
  k PC.knownRepr (CS.regValue re)

-- | This helper is required because the mapping that comes back from the macaw
-- ELF loader doesn't account for the TOC in PowerPC64.
toPPCAddrNameMap :: ( w ~ SAP.AddrWidth v
                    , MBLP.HasTOC (MP.AnyPPC v) (Elf.ElfHeaderInfo w)
                    )
                 => MBL.LoadedBinary (MP.AnyPPC v) (Elf.ElfHeaderInfo w)
                 -> MM.Memory w
                 -> [MMEL.MemSymbol w]
                 -> Map.Map (MM.MemSegmentOff w) BS8.ByteString
toPPCAddrNameMap loadedBinary mem elfSyms =
  Map.fromList [ (realSegOff, name)
               | (addr, name) <- Map.toList (MST.toAddrSymMap mem elfSyms)
               , Just realAddr <- return (MBLP.mapTOCEntryAddress toc (MM.segoffAddr addr))
               , Just realSegOff <- return (MM.asSegmentOff mem realAddr)
               ]
  where
    toc = MBLP.getTOC loadedBinary

mkSymExTest :: MST.SimulationResult -> MST.MemModelPreset -> FilePath -> TT.TestTree
mkSymExTest expected mmPreset exePath = TT.askOption $ \saveSMT@(SaveSMT _) -> TT.askOption $ \saveMacaw@(SaveMacaw _) -> TTH.testCaseSteps exePath $ \step -> do
  bytes <- BS.readFile exePath
  case Elf.decodeElfHeaderInfo bytes of
    Left (_, msg) -> TTH.assertFailure ("Error parsing ELF header from file '" ++ show exePath ++ "': " ++ msg)
    Right (Elf.SomeElf ehi) -> do
      case Elf.headerClass (Elf.header ehi) of
        Elf.ELFCLASS32 -> TTH.assertFailure "PPC32 is not supported yet due to ABI differences"
        Elf.ELFCLASS64 -> do
          loadedBinary <- MBL.loadBinary MMEL.defaultLoadOptions ehi
          symExTestSized expected mmPreset exePath saveSMT saveMacaw step ehi loadedBinary (MP.ppc64_linux_info loadedBinary)

data MacawPPCSymbolicData t = MacawPPCSymbolicData

symExTestSized :: forall v w arch
                . ( w ~ SAP.AddrWidth v
                  , 16 <= w
                  , 1 <= w
                  , SAP.KnownVariant v
                  , MM.MemWidth w
                  , MC.ArchConstraints arch
                  , arch ~ MP.AnyPPC v
                  , KnownNat w
                  , Show (Elf.ElfWordType w)
                  , MS.ArchInfo arch
                  , MBLP.HasTOC (MP.AnyPPC v) (Elf.ElfHeaderInfo w)
                  )
               => MST.SimulationResult
               -> MST.MemModelPreset
               -> FilePath
               -> SaveSMT
               -> SaveMacaw
               -> (String -> IO ())
               -> Elf.ElfHeaderInfo w
               -> MBL.LoadedBinary arch (Elf.ElfHeaderInfo w)
               -> MAI.ArchitectureInfo arch
               -> TTH.Assertion
symExTestSized expected mmPreset exePath saveSMT saveMacaw step ehi loadedBinary archInfo = do
   binfo <- MST.runDiscovery ehi exePath (toPPCAddrNameMap loadedBinary) archInfo
                             -- Test cases involving shared libraries are not
                             -- yet supported on the PowerPC backend. At a
                             -- minimum, this is blocked on
                             -- https://github.com/GaloisInc/elf-edit/issues/35.
                             (MMELP.noPLTStubInfo "PPC")
   let funInfos = Map.elems (MST.binaryDiscState (MST.mainBinaryInfo binfo) ^. M.funInfo)
   let testEntryPoints = mapMaybe hasTestPrefix funInfos
   F.forM_ testEntryPoints $ \(name, Some dfi) -> do
     step ("Testing " ++ BS8.unpack name ++ " at " ++ show (M.discoveredFunAddr dfi))
     writeMacawIR saveMacaw (BS8.unpack name) dfi
     Some (gen :: PN.NonceGenerator IO t) <- PN.newIONonceGenerator
     sym <- WEB.newExprBuilder WEB.FloatRealRepr MacawPPCSymbolicData gen
     CBO.withYicesOnlineBackend sym CBO.NoUnsatFeatures WPF.noFeatures $ \bak -> do
       -- We are using the z3 backend to discharge proof obligations, so
       -- we need to add its options to the backend configuration
       let solver = WS.z3Adapter
       let backendConf = WI.getConfiguration sym
       WC.extendConfig (WS.solver_adapter_config_options solver) backendConf

       execFeatures <- MST.defaultExecFeatures (MST.SomeOnlineBackend bak)
       archVals <- case MS.archVals (Proxy @(MP.AnyPPC v)) Nothing of
                     Just archVals -> pure archVals
                     Nothing -> error "symExTestSized: impossible"
       let extract = ppcResultExtractor archVals
       logger <- makeGoalLogger saveSMT solver name exePath
       let ?memOpts = LLVM.defaultMemOptions
       simRes <- MST.simulateAndVerify solver logger bak execFeatures archInfo archVals binfo mmPreset extract dfi
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
