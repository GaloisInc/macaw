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
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

-- | Pretty print an operator name and argumetns as an sexpr.
sexpr :: String -> [Doc] -> Doc
sexpr nm d = parens (hsep (text nm : d))

sexprA :: Applicative m => String -> [m Doc] -> m Doc
sexprA nm d = sexpr nm <$> sequenceA d

ppNat :: Applicative m => NatRepr n -> m Doc
ppNat n = pure (text (show n))
