{-# LANGUAGE TemplateHaskell #-}
module Data.Macaw.X86.Symbolic.Panic (
  P.panic,
  Component(..)
  ) where

import qualified Panic as P

data Component = X86_64
  deriving (Show)

instance P.PanicComponent Component where
  panicComponentName = show
  panicComponentIssues _ = "https://github.com/GaloisInc/macaw/issues"
  panicComponentRevision = $(P.useGitRevision)
