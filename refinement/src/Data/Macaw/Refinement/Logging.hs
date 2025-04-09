{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Refinement.Logging (
  RefinementLog(..)
  ) where

import qualified Control.Exception as X
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as MM
import qualified Prettyprinter as PP
import           Text.Printf ( printf )

data RefinementLog arch = RefiningTransferAt (MC.ArchSegmentOff arch)
                        | GeneratedModel Integer
                        | KillingSolverProcess
                        | KilledSolverProcess
                        | SymbolicExecutionError X.SomeException
                        | ResolvedAddresses [MC.ArchSegmentOff arch]

deriving instance (MM.MemWidth (MC.ArchAddrWidth arch)) => Show (RefinementLog arch)

instance (MM.MemWidth (MC.ArchAddrWidth arch)) => PP.Pretty (RefinementLog arch) where
  pretty l =
    case l of
      RefiningTransferAt addr -> PP.pretty ((printf "Refining transfer at %s" (show addr)) :: String)
      GeneratedModel addr -> PP.pretty ((printf "Generated model: 0x%x" addr) :: String)
      KillingSolverProcess -> PP.pretty "Killing solver process"
      KilledSolverProcess -> PP.pretty "Killed solver process"
      SymbolicExecutionError x -> PP.pretty (show x)
      ResolvedAddresses addrs ->
        PP.pretty "Resolved addresses: " <> PP.list (map (PP.pretty . show) addrs)
