module Data.Macaw.PPC.Rewrite (
  rewriteArchFn,
  rewriteArchStmt,
  rewriteArchTermStmt
  ) where

import Data.Macaw.CFG
import Data.Macaw.CFG.Rewriter

rewriteArchFn :: proxy ppc
              -> ArchFn ppc (Value ppc src) tp
              -> Rewriter ppc src tgt (Value ppc tgt tp)
rewriteArchFn = undefined

rewriteArchStmt :: proxy ppc
                -> ArchStmt ppc src
                -> Rewriter ppc src tgt ()
rewriteArchStmt = undefined

rewriteArchTermStmt :: proxy ppc
                    -> ArchTermStmt ppc src
                    -> Rewriter ppc src tgt (ArchTermStmt ppc tgt)
rewriteArchTermStmt = undefined
