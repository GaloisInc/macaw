{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
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

data MacawRefinementData t = MacawRefinementData

withNewBackend :: (MonadIO m)
               => Solver
               -> (forall proxy solver t st fs sym bak.
                      (sym ~ WE.ExprBuilder t st fs
                      , CB.IsSymBackend sym bak
                      , WPO.OnlineSolver solver) =>
                      proxy solver ->
                      WPF.ProblemFeatures ->
                      bak ->
                      m a)
               -> m a
withNewBackend s k = do
  sym <- liftIO $ WE.newExprBuilder WE.FloatUninterpretedRepr MacawRefinementData PN.globalNonceGenerator
  bak <- liftIO $ CBS.newSimpleBackend sym
  case s of
    CVC4 -> do
      let proxy = Proxy @(WPS.Writer WSC.CVC4)
      liftIO $ WC.extendConfig WSC.cvc4Options (WI.getConfiguration sym)
      let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs .|. WPF.useNonlinearArithmetic
      k proxy features bak
    Yices -> do
      let proxy = Proxy @WSY.Connection
      liftIO $ WC.extendConfig WSY.yicesOptions (WI.getConfiguration sym)
      -- For some reason, non-linear arithmetic is required for cvc4 and z3 but doesn't work at all with yices
      let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs .|. WPF.useLinearArithmetic
      k proxy features bak
    Z3 -> do
      let proxy = Proxy @(WPS.Writer WSZ.Z3)
      liftIO $ WC.extendConfig WSZ.z3Options (WI.getConfiguration sym)
      let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs .|. WPF.useNonlinearArithmetic
      k proxy features bak
