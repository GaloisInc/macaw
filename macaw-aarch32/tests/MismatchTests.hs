module MismatchTests where


import           Control.Monad.Catch
import qualified Data.ElfEdit as E
import           Data.Monoid
import           Shared
import           Test.Tasty
import           Test.Tasty.HUnit

import           Prelude


armMismatchTests :: [FilePath] -> TestTree
armMismatchTests badBinList =
    testGroup "ARM Mismatch Tests"
                   [ testGroup "BAD binaries" $ map testCorruptElf badBinList
                   ]

testCorruptElf :: FilePath -> TestTree
testCorruptElf fpath =
    testCase fpath $
             catch (withELF fpath
                       (\e -> do let (warn, _el) = E.getElf e
                                 flip assertBool (not (null warn)) $
                                   "ELF read of " ++ fpath ++ " should have failed."))
                   (\e -> case e of
                            ElfHeaderParseError _ _ _ -> return ()  -- tr '\0' '8' test-just-exit.exe
                            ElfParseError _ _         -> return ()  -- tr '\05' '8' test-just-exit.exe
                            other -> assertFailure $ "Unexpected exception: " <> show other)


{-
$ cat test-just-exit.exe | tr '\034' '8' > test-just-exit8.exe=bad
== Result throws "error" instead of returning an parse failure.
-}
