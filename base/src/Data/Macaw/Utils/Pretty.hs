{-|
This defines some utility functions for pretty-printing declarations.
-}
module Data.Macaw.Utils.Pretty
  ( sexpr
  , sexprA
  ) where

import           Prettyprinter

-- | Pretty print an operator name and arguments as an sexpr.
sexpr :: String -> [Doc ann] -> Doc ann
sexpr nm d = parens (hsep (pretty nm : d))

sexprA :: Applicative m => String -> [m (Doc ann)] -> m (Doc ann)
sexprA nm d = sexpr nm <$> sequenceA d