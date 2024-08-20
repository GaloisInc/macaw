{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Lang.Crucible.CLI.Options qualified as Opts

import Data.Macaw.X86.Symbolic.CLI (withX86Hooks)

main :: IO ()
main = withX86Hooks (Opts.main "macaw-x86")
