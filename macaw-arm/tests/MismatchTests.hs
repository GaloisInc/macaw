module MismatchTests where


import Test.Tasty
import Test.Tasty.HUnit
import Shared
import Data.Monoid
import Control.Monad.Catch


armMismatchTests :: [FilePath] -> TestTree
armMismatchTests badBinList =
    testGroup "ARM Mismatch Tests"
                   [ testGroup "BAD binaries" $ map testCorruptElf badBinList
                   ]

testCorruptElf :: FilePath -> TestTree
testCorruptElf fpath =
    testCase fpath $
             catch (withELF fpath (const $ assertFailure "ELF read should have failed"))
                       (\e -> case e of
                               ElfHeaderParseError _ _ _ -> return ()  -- tr '\0' '8' test-just-exit.exe
                               ElfParseError _ _         -> return ()  -- tr '\05' '8' test-just-exit.exe
                               other -> assertFailure $ "Unexpected exception: " <> show other)


{-
$ cat test-just-exit.exe | tr '\034' '8' > test-just-exit8.exe=bad
== Result throws "error" instead of returning an parse failure.
-}
