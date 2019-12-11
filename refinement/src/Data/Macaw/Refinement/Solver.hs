{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Macaw.Refinement.Solver (
  Solver(..)
  , withNewBackend
  ) where

import           Control.Monad.Trans ( MonadIO, liftIO )
import           Data.Bits ( (.|.) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Parameterized.Nonce as PN
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Simple as CBS
import qualified What4.Config as WC
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTLib2 as WPS
import qualified What4.ProblemFeatures as WPF
import qualified What4.Solver.CVC4 as WSC
import qualified What4.Solver.Yices as WSY
import qualified What4.Solver.Z3 as WSZ

data Solver = CVC4 | Yices | Z3
  deriving (Read, Show, Eq, Ord)

withNewBackend :: (MonadIO m)
               => Solver
               -> (forall proxy t solver fs sym . (sym ~ CBS.SimpleBackend t fs, CB.IsSymInterface sym, WPO.OnlineSolver t solver) => proxy solver -> WPF.ProblemFeatures -> sym -> m a)
               -> m a
withNewBackend s k = do
  sym :: CBS.SimpleBackend PN.GlobalNonceGenerator (WE.Flags WE.FloatUninterpreted)
      <- liftIO $ CBS.newSimpleBackend WE.FloatUninterpretedRepr PN.globalNonceGenerator
  case s of
    CVC4 -> do
      let proxy = Proxy @(WPS.Writer WSC.CVC4)
      liftIO $ WC.extendConfig WSC.cvc4Options (WI.getConfiguration sym)
      let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs .|. WPF.useNonlinearArithmetic
      k proxy features sym
    Yices -> do
      let proxy = Proxy @(WSY.Connection PN.GlobalNonceGenerator)
      liftIO $ WC.extendConfig WSY.yicesOptions (WI.getConfiguration sym)
      -- For some reason, non-linear arithmetic is required for cvc4 and z3 but doesn't work at all with yices
      let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs
      k proxy features sym
    Z3 -> do
      let proxy = Proxy @(WPS.Writer WSZ.Z3)
      liftIO $ WC.extendConfig WSZ.z3Options (WI.getConfiguration sym)
      let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs .|. WPF.useNonlinearArithmetic
      k proxy features sym
