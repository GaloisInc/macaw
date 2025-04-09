{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.List (sort)
import Data.Proxy (Proxy(Proxy))
import Data.Text.IO qualified as T
import System.FilePath
import System.IO

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

import Lang.Crucible.Syntax.Prog (doParseCheck)

import Data.Macaw.Symbolic.Syntax (machineCodeParserHooks)

import Data.Macaw.ARM (ARM)
import Data.Macaw.AArch32.Symbolic ()  -- TraversableFC instance for (MacawExt ARM) statements and expressions
import Data.Macaw.AArch32.Symbolic.Syntax (aarch32ParserHooks)

main :: IO ()
main = do
  parseTests <- findTests "Parse tests" "test-data" testParser
  defaultMain $ testGroup "Tests" [parseTests]

findTests :: String -> FilePath -> (FilePath -> FilePath -> IO ()) -> IO TestTree
findTests groupName testDir testAction =
  do inputs <- findByExtension [".cbl"] testDir
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

testParser :: FilePath -> FilePath -> IO ()
testParser inFile outFile =
  do contents <- T.readFile inFile
     let ?parserHooks = machineCodeParserHooks (Proxy @ARM) aarch32ParserHooks
     withFile outFile WriteMode $ doParseCheck inFile contents True

