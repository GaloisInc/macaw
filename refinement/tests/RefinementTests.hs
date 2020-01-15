-- This test harness uses local files to run Macaw discovery both with
-- and without refinement and checks the results of that validation
-- against expected outputs (aka. golden testing).
--
-- test/samples/
--    X[.A].[F-]expected       -- expected (golden) output [the primary file that enables this test]
--    X.A.exe                  -- input ELF binary file
--    X.c                      -- C source for generating binary
--
-- This methodology allows a binary for each architecture (A) to be
-- produced from a single C source (X), and then one or more
-- refinement test forms (F) to be created to run on that binary,
-- where F is one of:
--
--    "base"    -- standard Macaw discovery
--    "refined" -- additional discovery from this macaw-refinement package
--
-- If there is no "F-" portion, then the same expected file is applied
-- for all possible values of F.
--
-- If there is an expected file but it fails to Parse on a Haskell
-- Read (e.g. "echo garbage > blah.ppc.base-expected") then the test
-- will write the actual output to a separate file with the
-- "last-actual" suffix (e.g. "blah.ppc.base-last-actual"); verify the
-- contents of that file and then simply copy them to the expected
-- file to get the correct file contents.
--
-- There is also a README in the test/samples directory where the C
-- source is described, along with various tests.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main ( main ) where

import           Control.Monad ( when )
import qualified Data.Foldable as F
import qualified Data.Macaw.Refinement as MR
import qualified Data.Map as M
import           Data.Maybe ( catMaybes )
import           Data.Proxy ( Proxy(..) )
import           Data.Semigroup ( (<>) )
import qualified Data.Set as Set
import           Data.Tagged
import           Data.Typeable ( Typeable )
import           Data.Word ( Word64 )
import           Options.Applicative
import qualified System.Directory as SD
import           System.FilePath ( (</>), (<.>) )
import qualified System.FilePath.Glob as FPG
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import           Test.Tasty.Ingredients as TI
import           Test.Tasty.Options
import           Text.Read ( readEither )
import           Text.Printf ( printf )

import           Prelude

import           Initialization ( withElf, withRefinedDiscovery )
import           Summary ( blockAddresses )
import           Options ( Options(..) )

datadir :: FilePath
datadir =  "tests/samples"

data ShowSearch =  ShowSearch Bool deriving (Eq, Ord, Typeable)

instance IsOption ShowSearch where
  defaultValue = ShowSearch False
  parseValue = fmap ShowSearch . safeRead
  optionName = pure $ "showsearch"
  optionHelp = pure $ "Show details of the search for the set of\n\
                      \refinement tests that would be performed\n\
                      \based on the contents of the " <> datadir <> " directory"
  optionCLParser = ShowSearch <$> switch
                      ( long (untag (optionName :: Tagged ShowSearch String))
                      <> help (untag (optionHelp :: Tagged ShowSearch String))
                      )

data VerboseLogging = VerboseLogging Bool
  deriving (Eq, Ord)

instance IsOption VerboseLogging where
  defaultValue = VerboseLogging False
  parseValue = fmap VerboseLogging . safeRead
  optionName = pure "verbose-logging"
  optionHelp = pure "Turn on verbose logging output"
  optionCLParser = VerboseLogging <$> switch ( long (untag (optionName :: Tagged VerboseLogging String))
                                             <> help (untag (optionHelp :: Tagged VerboseLogging String))
                                             )


-- | This is a Tasty "Ingredient" (aka test runner) that can be used
-- to display the search process and results for generating the tests.
searchResultsReport :: TI.Ingredient
searchResultsReport = TestManager [] $ \opts _tests ->
  if lookupOption opts == ShowSearch True
  then Just $ do searchlist <- getTestList datadir True
                 putStrLn ""
                 putStrLn $ "Final set of tests [" ++ show (length searchlist) ++ "]:"
                 mapM_ (putStrLn . show) searchlist
                 putStrLn ""
                 putStrLn ("These search results were based on the contents of the " <>
                           datadir <> " directory\n\
                           \Syntax:  BASENAME.c\n\
                           \         BASENAME.exe\n\
                           \         BASENAME.exe.expected\n\
                           \Note that if any .expected file fails a Haskell Read\n\
                           \parse, a \".....last-actual\" file is written; it can\n\
                           \be verified and renamed to be the new expected contents.\n")

                 return True
  else Nothing


ingredients :: [TI.Ingredient]
ingredients = TT.includingOptions [ Option (Proxy :: Proxy ShowSearch)
                                  , Option (Proxy :: Proxy VerboseLogging)
                                  ]
              : searchResultsReport
              : TT.defaultIngredients

main :: IO ()
main = do
  -- Note: dynamic test generation should be done before the
  -- TT.defaultMain call, but test arguments/options are not yet
  -- available for this; see:
  -- https://stackoverflow.com/questions/33040722
  -- https://github.com/feuerbach/tasty/issues/228
  testInputs <- getTestList datadir False
  -- let testNames = Set.fromList (map name testInputs)
  TT.defaultMainWithIngredients ingredients $
    TT.testGroup "macaw-refinement" $ (map mkTest testInputs)

data TestInput = TestInput { binaryFilePath :: FilePath
                           , expectedFilePath :: FilePath
                           }
               deriving (Eq, Show)

-- | Returns a list of the TestInputs that should be run.  These are
-- driven by the existence of a .[F-]expected file, for which there
-- should be a corresponding .exe.  The exe and expected files are
-- sub-named by the architecture (A) to which they apply.
getTestList :: FilePath -> Bool -> IO [TestInput]
getTestList basedir explain = do
  when explain $ putStrLn $ "Checking for test inputs in " <> (basedir </> "*.exe")

  -- Find all of the executables we have available
  exeNames <- FPG.namesMatching (basedir </> "*.exe")

  -- For each executable, produce a TestInput iff it has an associated .expected file
  catMaybes <$> mapM findExpectedFiles exeNames
  where
    findExpectedFiles exeName = do
      let expectedFilename = exeName <.> "expected"
      SD.doesFileExist expectedFilename >>= \case
        True -> return $ Just TestInput { binaryFilePath = exeName
                                        , expectedFilePath = expectedFilename
                                        }
        False -> return Nothing

-- Refinement configuration for the test suite
testOptions :: Bool -> FilePath -> Options
testOptions verb file = Options { inputFile = file
                                , unrefined = False
                                , summaryOnly = False
                                , verbose = verb
                                , solver = MR.Yices
                                , solverInteractionFile = Nothing
                                , maximumModelCount = 20
                                , threadCount = 1
                                , timeoutSeconds = 60
                                }

mkTest :: TestInput -> TT.TestTree
mkTest testinp = do
  TT.askOption $ \(VerboseLogging beVerbose) -> TTH.testCase (binaryFilePath testinp) $ do
    let opts = testOptions beVerbose (binaryFilePath testinp)
    withElf opts $ \archInfo bin _unrefinedDI -> do
      withRefinedDiscovery opts archInfo bin $ \refinedDI _refinedInfo -> do
        let actual = blockAddresses refinedDI
        expectedInput <- readFile (expectedFilePath testinp)
        case readEither expectedInput of
          Left err -> TTH.assertFailure (printf "Failed to parse expected input file [%s]: %s" (expectedFilePath testinp) err)
          Right (expected :: [(Word64, [Word64])]) -> do
            -- We iterate over the *expected* functions so that we can just
            -- specify expected results for interesting bits and ignore the
            -- other discovered functions.
            F.forM_ expected $ \(faddr, expectedBlockAddrs) -> do
              let expectedAddrSet = Set.fromList expectedBlockAddrs
              case M.lookup faddr actual of
                Nothing -> TTH.assertFailure (printf "Missing expected function at address 0x%x" faddr)
                Just actualBlockAddrs -> do
                  F.forM_ expectedBlockAddrs $ \expectedBlockAddr -> do
                    let msg = printf "Missing expected block at 0x%x in function 0x%x" expectedBlockAddr faddr
                    TTH.assertBool msg (Set.member expectedBlockAddr actualBlockAddrs)
                  F.forM_ actualBlockAddrs $ \actualBlockAddr -> do
                    let msg = printf "Found an unexpected block in the binary at 0x%x in function 0x%x" actualBlockAddr faddr
                    TTH.assertBool msg (Set.member actualBlockAddr expectedAddrSet)

