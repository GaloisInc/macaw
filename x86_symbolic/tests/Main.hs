{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ElfEdit as Elf
import qualified Data.Foldable as F
import           Data.Maybe ( mapMaybe )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import           System.FilePath ( (</>), (<.>) )
import qualified System.FilePath.Glob as SFG
import qualified System.IO as IO
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import qualified Test.Tasty.Options as TTO
import qualified Test.Tasty.Runners as TTR

import qualified Data.Macaw.Discovery as M
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Testing as MST
import qualified Data.Macaw.X86 as MX
import           Data.Macaw.X86.Symbolic ()
import qualified What4.ProblemFeatures as WPF
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Simulator as CS

-- | A Tasty option to tell us to save SMT queries and responses to /tmp for debugging purposes
data SaveSMT = SaveSMT Bool
  deriving (Eq, Show)

instance TTO.IsOption SaveSMT where
  defaultValue = SaveSMT False
  parseValue v = SaveSMT <$> TTO.safeReadBool v
  optionName = pure "save-smt"
  optionHelp = pure "Save SMT sessions to files in /tmp for debugging"

ingredients :: [TTR.Ingredient]
ingredients = TT.includingOptions [ TTO.Option (Proxy @SaveSMT)
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

-- | X86_64 functions with a single scalar return value return it in %rax
--
-- Since all test functions must return a value to assert as true, this is
-- straightforward to extract
x86ResultExtractor :: (CB.IsSymInterface sym) => MS.ArchVals MX.X86_64 -> MST.ResultExtractor sym MX.X86_64
x86ResultExtractor archVals = MST.ResultExtractor $ \regs _sp _mem k -> do
  let re = MS.lookupReg archVals regs MX.RAX
  k PC.knownRepr (CS.regValue re)

mkSymExTest :: MST.SimulationResult -> FilePath -> TT.TestTree
mkSymExTest expected exePath = TT.askOption $ \saveSMT@(SaveSMT _) -> TTH.testCaseSteps exePath $ \step -> do
  bytes <- BS.readFile exePath
  case Elf.decodeElfHeaderInfo bytes of
    Left (_, msg) -> TTH.assertFailure ("Error parsing ELF header from file '" ++ show exePath ++ "': " ++ msg)
    Right (Elf.SomeElf ehi) -> do
      case Elf.headerClass (Elf.header ehi) of
        Elf.ELFCLASS32 -> TTH.assertFailure "32 bit x86 binaries are not supported"
        Elf.ELFCLASS64 -> do
          (mem, funInfos) <- MST.runDiscovery ehi MX.x86_64_linux_info
          let testEntryPoints = mapMaybe hasTestPrefix funInfos
          F.forM_ testEntryPoints $ \(name, Some dfi) -> do
            step ("Testing " ++ BS8.unpack name)
            Some (gen :: PN.NonceGenerator IO t) <- PN.newIONonceGenerator
            CBO.withYicesOnlineBackend CBO.FloatRealRepr gen CBO.NoUnsatFeatures WPF.noFeatures $ \sym -> do
              execFeatures <- MST.defaultExecFeatures (MST.SomeOnlineBackend sym)
              let Just archVals = MS.archVals (Proxy @MX.X86_64)
              let extract = x86ResultExtractor archVals
              let solver = WS.yicesAdapter
              logger <- makeGoalLogger saveSMT solver name exePath
              simRes <- MST.simulateAndVerify solver logger sym execFeatures MX.x86_64_linux_info archVals mem extract dfi
              TTH.assertEqual "AssertionResult" expected simRes

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
    escapeSlash '/' = '_'
    escapeSlash c = c
