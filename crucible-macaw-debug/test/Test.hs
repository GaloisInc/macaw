{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>

NOTE: Much of this is duplicated from the crucible-debug test suite. It would be
nice to share it, but it's not currently exported.

This test suite is composed of golden test files.
Each file consists of inputs (@Statement@s) that begin with @> @, and outputs
that follow them. This comingling of inputs and outputs stands in contrast to a
more customary golden test setup where the inputs are in one file and the outputs
in another. It makes the relationship between various inputs and outputs clear at
a glance, which makes the tests easier to read and understand in a text editor or
web interface. This readability comes at the cost of a mildly gnarly test harness
(see, e.g., 'parseTest' and 'runScript').
To create a new test, simply create a new file with all of the input lines, and
then run the test suite with the @--accept@ flag, i.e.,
@cabal test crucible-macaw-debug-tests -- --accept@.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Applicative qualified as Applicative
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as BS
import Data.IORef qualified as IORef
import Data.List qualified as List
import Data.Parameterized.Map qualified as MapF
import Data.Proxy (Proxy(..))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text.IO qualified as IO
import Lang.Crucible.Debug qualified as Debug
import Lang.Crucible.Debug.Inputs qualified as Inps
import Lang.Crucible.Debug.Outputs qualified as Outps
import Lang.Crucible.FunctionHandle qualified as CFH
import Lang.Crucible.LLVM.MemModel qualified as Mem
import Lang.Crucible.Pretty (IntrinsicPrinters(..))
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.Syntax.Concrete (ParserHooks(..))
import Prettyprinter qualified as PP
import Prettyprinter.Render.Text qualified as PP
import System.Directory qualified as Dir
import Test.Tasty qualified as Tasty
import Test.Tasty.Golden qualified as Golden

import Data.Macaw.Symbolic qualified as Macaw
import Data.Macaw.Symbolic.Debug qualified as MacawDebug
import Data.Macaw.X86 qualified as X86
import Data.Macaw.X86.Symbolic ()  -- instance GenArchInfo

testDir :: FilePath
testDir = "test-data/"

-- | Parse a test file into a sequence of inputs and outputs
parseTest :: Text -> [(Text, Text)]
parseTest txt = List.reverse (go [] Nothing (Text.lines txt))
  where
    go ::
      -- | Accumulated result
      [(Text, Text)] ->
      -- | Perhaps (input, accumulated output)
      Maybe (Text, [Text]) ->
      -- | Remaining lines
      [Text] ->
      [(Text, Text)]
    go accum Nothing [] = accum
    go accum (Just (inp, out)) [] = (inp, Text.unlines (List.reverse out)) : accum
    go accum soFar (l:ls) =
      if l == ""
      then go accum soFar ls
      else
        case (soFar, Text.stripPrefix "> " l) of
          (Nothing, Nothing) -> error "Ill-formed test file"
          (Nothing, Just l') -> go accum (Just (l', [])) ls
          (Just (inp, out), Nothing) -> go accum (Just (inp, l:out)) ls
          (Just (inp, out), Just l') ->
            let accum' = (inp, Text.unlines (List.reverse out)) : accum in
            go accum' (Just (l', [])) ls

-- | A stub ExtensionImpl for MacawExt that errors if any extension
-- statement or expression is actually evaluated. This is fine for tests that
-- only exercise the debugger command interface (help, usage, etc.) without
-- actually running Macaw machine code.
stubMacawExtImpl :: C.ExtensionImpl p sym (Macaw.MacawExt X86.X86_64)
stubMacawExtImpl = C.ExtensionImpl
  { C.extensionEval = \_ _ _ _ -> \_ -> error "macaw extensionEval: not needed for debugger command tests"
  , C.extensionExec = \_ _ -> error "macaw extensionExec: not needed for debugger command tests"
  }

runScript :: FilePath -> IO ByteString
runScript path = do
  halloc <- CFH.newHandleAllocator
  mVar <- Mem.mkMemVar "crucible-macaw-debug:mem" halloc

  archVals <- case Macaw.archVals (Proxy @X86.X86_64) Nothing of
    Just v -> pure v
    Nothing -> error "failed to obtain X86_64 archVals"
  let cmdExt = MacawDebug.macawCommandExt archVals

  testTxt <- IO.readFile path
  let parsed = parseTest testTxt
  let inputTxtLines = map fst parsed ++ ["done"]
  inps <- Inps.parseInputs cmdExt <$> Inps.prepend inputTxtLines Inps.fail
  r <- IORef.newIORef []
  let logger = \_ -> pure ()
  let ?parserHooks = ParserHooks Applicative.empty Applicative.empty
  Debug.bareDebuggerExt
    cmdExt
    (MacawDebug.macawExtImpl (IntrinsicPrinters MapF.empty) mVar archVals Nothing Nothing)
    stubMacawExtImpl
    inps
    (Outps.accumulate r)
    logger
  outs <- List.reverse <$> IORef.readIORef r
  let outsTxt = map (PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions . PP.pretty) outs
  let inOuts = zipWith (\i o -> "> " <> i <> "\n\n" <> o <> "\n") inputTxtLines outsTxt
  pure (Text.encodeUtf8 (Text.unlines inOuts))

mkTest :: FilePath -> FilePath -> Tasty.TestTree
mkTest dir path =
  Golden.goldenVsStringDiff
  path
  (\x y -> ["diff", "-u", x, y])
  (dir ++ path)
  (BS.fromStrict <$> runScript (dir ++ path))

loadTests :: FilePath -> IO Tasty.TestTree
loadTests dir = do
  -- This `List.sort` is not technically necessary, it just ensures that test
  -- cases will be performed in a stable ordering, since `Dir.listDirectory`
  -- doesn't guarantee such an ordering.
  files <- List.sort <$> Dir.listDirectory dir
  let dbgScripts = List.filter (".txt" `List.isSuffixOf`) files
  let tests = map (uncurry mkTest) (map (dir,) dbgScripts)
  pure (Tasty.testGroup dir tests)

main :: IO ()
main = do
  mainTests <- loadTests testDir
  let tests = [mainTests]
  Tasty.defaultMain (Tasty.testGroup "Tests" tests)
