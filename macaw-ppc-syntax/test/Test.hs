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
import GHC.TypeNats (KnownNat, type (<=))
import System.FilePath
import System.FilePath.Glob qualified as Glob
import System.IO

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

import Lang.Crucible.Syntax.Prog (doParseCheck)

import Data.Macaw.Memory qualified as DMM
import Data.Macaw.Symbolic.Syntax (machineCodeParserHooks)
import SemMC.Architecture.PPC qualified as SAP

import Data.Macaw.PPC qualified as PPC
import Data.Macaw.PPC.Symbolic.Syntax (ppcParserHooks)

main :: IO ()
main = do
  ppc32Tests <- ppcTests PPC.V32Repr
  ppc64Tests <- ppcTests PPC.V64Repr
  defaultMain $ testGroup "Tests" [ppc32Tests, ppc64Tests]

ppcVariantName :: PPC.VariantRepr v -> String
ppcVariantName PPC.V32Repr = "PPC32"
ppcVariantName PPC.V64Repr = "PPC64"

ppcFileExt :: PPC.VariantRepr v -> String
ppcFileExt PPC.V32Repr = "ppc32.cbl"
ppcFileExt PPC.V64Repr = "ppc64.cbl"

ppcTests ::
  ( KnownNat (SAP.AddrWidth v)
  , PPC.KnownVariant v
  , 1 <= SAP.AddrWidth v
  , DMM.MemWidth (SAP.AddrWidth v)
  ) =>
  PPC.VariantRepr v ->
  IO TestTree
ppcTests v =
  let groupName = ppcVariantName v ++ " parse tests" in
  findTests v groupName "test-data" (testParser v)

findTests ::
  PPC.VariantRepr v ->
  String ->
  FilePath ->
  (FilePath -> FilePath -> IO ()) ->
  IO TestTree
findTests v groupName testDir testAction =
  do inputs <- Glob.glob (testDir </> "*" <.> ppcFileExt v)
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
  forall v.
  ( KnownNat (SAP.AddrWidth v)
  , PPC.KnownVariant v
  , 1 <= SAP.AddrWidth v
  , DMM.MemWidth (SAP.AddrWidth v)
  ) =>
  PPC.VariantRepr v ->
  FilePath ->
  FilePath ->
  IO ()
testParser v inFile outFile =
  do contents <- T.readFile inFile
     let ?parserHooks = machineCodeParserHooks (Proxy @(PPC.AnyPPC v)) (ppcParserHooks v)
     withFile outFile WriteMode $ doParseCheck inFile contents True
