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
import qualified System.FilePath.Glob as SFG
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH

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

main :: IO ()
main = do
  testFilePaths <- SFG.glob "tests/*.exe"
  let tests = TT.testGroup "Binary Tests" (map mkSymExTest testFilePaths)
  TT.defaultMain tests

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

mkSymExTest :: FilePath -> TT.TestTree
mkSymExTest exePath = TTH.testCaseSteps exePath $ \step -> do
  bytes <- BS.readFile exePath
  case Elf.decodeElfHeaderInfo bytes of
    Left (_, msg) -> TTH.assertFailure ("Error parsing ELF header from file '" ++ show exePath ++ "': " ++ msg)
    Right (Elf.SomeElf ehi) -> do
      Elf.ELFCLASS64 <- return (Elf.headerClass (Elf.header ehi))
      (mem, funInfos) <- MST.runDiscovery ehi MX.x86_64_linux_info
      let testEntryPoints = mapMaybe hasTestPrefix funInfos
      F.forM_ testEntryPoints $ \(name, Some dfi) -> do
        step ("Testing " ++ BS8.unpack name)
        Some (gen :: PN.NonceGenerator IO t) <- PN.newIONonceGenerator
        CBO.withYicesOnlineBackend CBO.FloatRealRepr gen CBO.NoUnsatFeatures WPF.noFeatures $ \sym -> do
          execFeatures <- MST.defaultExecFeatures (MST.SomeOnlineBackend sym)
          let Just archVals = MS.archVals (Proxy @MX.X86_64)
          let extract = x86ResultExtractor archVals
          simRes <- MST.simulateAndVerify WS.yicesAdapter sym execFeatures MX.x86_64_linux_info archVals mem extract dfi
          TTH.assertEqual "AssertionResult" (MST.SimulationResult MST.Unsat) simRes
