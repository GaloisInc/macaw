{-|
Copyright        : (c) Galois, Inc 2018
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines some utility functions for pretty-printing declarations.
-}
module Data.Macaw.Utils.Pretty
  ( ppNat
  , sexpr
  , sexprA
  ) where

import           Data.Parameterized.NatRepr
import           Prettyprinter

-- | Pretty print an operator name and argumetns as an sexpr.
sexpr :: String -> [Doc ann] -> Doc ann
sexpr nm d = parens (hsep (pretty nm : d))

sexprA :: Applicative m => String -> [m (Doc ann)] -> m (Doc ann)
sexprA nm d = sexpr nm <$> sequenceA d

ppNat :: Applicative m => NatRepr n -> m (Doc ann)
ppNat n = pure (viaShow n)
