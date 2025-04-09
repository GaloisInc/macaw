{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main (main) where

import Data.List (sort)
import Data.Proxy (Proxy(Proxy))
import Data.Text.IO qualified as T
import System.FilePath
import System.FilePath.Glob qualified as Glob
import System.IO

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

import Lang.Crucible.Syntax.Prog (doParseCheck)

import Data.Macaw.Symbolic.Syntax (machineCodeParserHooks)
import qualified GRIFT.Types as G

import Data.Macaw.RISCV qualified as DMR
import Data.Macaw.RISCV.Symbolic.Syntax (riscvParserHooks)

main :: IO ()
main = do
  riscv32Tests <- riscvTests G.rv32GCRepr
  riscv64Tests <- riscvTests G.rv64GCRepr
  defaultMain $ testGroup "Tests" [riscv32Tests, riscv64Tests]

riscvVariantName :: G.RVRepr rv -> String
riscvVariantName (G.RVRepr baseArch _) =
  case baseArch of
    G.RV32Repr -> "RISCV32"
    G.RV64Repr -> "RISCV64"
    G.RV128Repr -> error "riscvVariantName: RV128 not yet supported"

riscvFileExt :: G.RVRepr rv -> String
riscvFileExt (G.RVRepr baseArch _) =
  case baseArch of
    G.RV32Repr -> "riscv32.cbl"
    G.RV64Repr -> "riscv64.cbl"
    G.RV128Repr -> error "riscvFileExt: RV128 not yet supported"

riscvTests ::
  (G.KnownRV rv, DMR.RISCVConstraints rv) =>
  G.RVRepr rv ->
  IO TestTree
riscvTests rv =
  let groupName = riscvVariantName rv ++ " parse tests" in
  findTests rv groupName "test-data" (testParser rv)

findTests ::
  G.RVRepr rv ->
  String ->
  FilePath ->
  (FilePath -> FilePath -> IO ()) ->
  IO TestTree
findTests rv groupName testDir testAction =
  do inputs <- Glob.glob (testDir </> "*" <.> riscvFileExt rv)
     return $ testGroup groupName
       [ goldenFileTestCase input testAction
       | input <- sort inputs
       ]

goldenFileTestCase :: FilePath -> (FilePath -> FilePath -> IO ()) -> TestTree
goldenFileTestCase input testAction =
  goldenVsFileDiff
   (takeBaseName input) -- test name
   (\x y -> ["diff", "-u", x, y])
   goodFile -- golden file path
   outFile
   (testAction input outFile) -- action whose result is tested
  where
    outFile = replaceExtension input ".out"
    goodFile = replaceExtension input ".out.good"

testParser ::
  forall rv.
  (G.KnownRV rv, DMR.RISCVConstraints rv) =>
  G.RVRepr rv ->
  FilePath ->
  FilePath ->
  IO ()
testParser rv inFile outFile =
  do contents <- T.readFile inFile
     let ?parserHooks = machineCodeParserHooks (Proxy @(DMR.RISCV rv)) (riscvParserHooks rv)
     withFile outFile WriteMode $ doParseCheck inFile contents True
