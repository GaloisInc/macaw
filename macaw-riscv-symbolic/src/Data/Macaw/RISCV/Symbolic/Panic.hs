{-# LANGUAGE TemplateHaskell #-}
module Data.Macaw.RISCV.Symbolic.Panic (
  P.panic,
  Component(..)
  ) where

import qualified Panic as P

data Component = RISCV
  deriving (Show)

instance P.PanicComponent Component where
  panicComponentName = show
  panicComponentIssues _ = "https://github.com/GaloisInc/macaw/issues"
  panicComponentRevision = $(P.useGitRevision)
