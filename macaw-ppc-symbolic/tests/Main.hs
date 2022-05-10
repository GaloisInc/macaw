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
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Testing as MST
import qualified Data.Macaw.PPC as MP
import           Data.Macaw.PPC.Symbolic ()
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

main :: IO ()
main = do
  -- These are pass/fail in that the assertions in the "pass" set are true (and
  -- the solver returns Unsat), while the assertions in the "fail" set are false
  -- (and the solver returns Sat).
  passTestFilePaths <- SFG.glob "tests/pass/*.exe"
  failTestFilePaths <- SFG.glob "tests/fail/*.exe"
  let passRes = MST.SimulationResult MST.Unsat
  let failRes = MST.SimulationResult MST.Sat
  let passTests = TT.testGroup "True assertions" (map (mkSymExTest passRes) passTestFilePaths)
  let failTests = TT.testGroup "False assertions" (map (mkSymExTest failRes) failTestFilePaths)
  TT.defaultMainWithIngredients ingredients (TT.testGroup "Binary Tests" [passTests, failTests])

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
ppcResultExtractor archVals = MST.ResultExtractor $ \regs _sp _mem k -> do
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

mkSymExTest :: MST.SimulationResult -> FilePath -> TT.TestTree
mkSymExTest expected exePath = TT.askOption $ \saveSMT@(SaveSMT _) -> TT.askOption $ \saveMacaw@(SaveMacaw _) -> TTH.testCaseSteps exePath $ \step -> do
  bytes <- BS.readFile exePath
  case Elf.decodeElfHeaderInfo bytes of
    Left (_, msg) -> TTH.assertFailure ("Error parsing ELF header from file '" ++ show exePath ++ "': " ++ msg)
    Right (Elf.SomeElf ehi) -> do
      case Elf.headerClass (Elf.header ehi) of
        Elf.ELFCLASS32 -> TTH.assertFailure "PPC32 is not supported yet due to ABI differences"
        Elf.ELFCLASS64 -> do
          loadedBinary <- MBL.loadBinary MMEL.defaultLoadOptions ehi
          symExTestSized expected exePath saveSMT saveMacaw step ehi loadedBinary (MP.ppc64_linux_info loadedBinary)

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
                  , MS.ArchInfo arch
                  , MBLP.HasTOC (MP.AnyPPC v) (Elf.ElfHeaderInfo w)
                  )
                => MST.SimulationResult
               -> FilePath
               -> SaveSMT
               -> SaveMacaw
               -> (String -> IO ())
               -> Elf.ElfHeaderInfo w
               -> MBL.LoadedBinary arch (Elf.ElfHeaderInfo w)
               -> MAI.ArchitectureInfo arch
               -> TTH.Assertion
symExTestSized expected exePath saveSMT saveMacaw step ehi loadedBinary archInfo = do
   (mem, discState) <- MST.runDiscovery ehi (toPPCAddrNameMap loadedBinary) archInfo
   let funInfos = Map.elems (discState ^. M.funInfo)
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
       let Just archVals = MS.archVals (Proxy @(MP.AnyPPC v)) Nothing
       let extract = ppcResultExtractor archVals
       logger <- makeGoalLogger saveSMT solver name exePath
       let ?memOpts = LLVM.defaultMemOptions
       simRes <- MST.simulateAndVerify solver logger bak execFeatures archInfo archVals mem extract discState dfi
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
