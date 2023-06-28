{-|
Defines specialized monads for collecting logging information while
performing discovery
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}

module Data.Macaw.Discovery.DiscoveryM
        (
          MonadDiscoveryTrace(..)
        , DiscoverySTL
        , DiscoverySTS
        , DiscoveryT
        , runDiscoveryT
        , discoverySTStoSTL
        , discoverySTLtoSTS
        , runDiscoverySTL
        , runDiscoverySTS
        , showSimpleTrace
        , emitDiscoveryTrace
        -- re-exports
        , DiscoveryTrace
        , discoveryTrace
        , DiscoveryTraceData(..)
        , traceValues
        ) where
import Control.Monad.Writer.Strict
import GHC.Stack
import Data.Functor.Identity
import Control.Monad.Reader
import qualified Control.Monad.ST.Lazy as STL
import qualified Control.Monad.ST.Strict as STS
import qualified Data.STRef.Lazy as STL
import qualified Data.STRef.Strict as STS
import Data.Macaw.Discovery.ParsedContents
import Data.Parameterized
import Data.Macaw.CFG.Core (Value)


class Monad m => MonadDiscoveryTrace arch m | m -> arch where
  -- | Add the given traces to the current trace
  emitDiscoveryTraces :: [DiscoveryTrace arch] -> m ()
  -- | Nest the tracing results from the sub-computation in
  --   a 'NestedTraceData', and drop them from the outer trace
  withDiscoveryTracing :: DiscoveryTraceData arch ids s -> m a -> m a

traceValues :: HasCallStack => MonadDiscoveryTrace arch m => [(String, Some (Value arch ids))] -> m ()
traceValues vals = forM_ vals $ \(nm,Some v) -> emitDiscoveryTrace $ MacawValue nm v

newtype DiscoveryT arch m a = DiscoveryT { unDiscoveryT :: WriterT ([DiscoveryTrace arch]) m a }
  deriving (MonadTrans, Functor, Applicative)

runDiscoveryT :: DiscoveryT arch m a -> m (a, [DiscoveryTrace arch])
runDiscoveryT (DiscoveryT f) = runWriterT f

deriving instance Monad m => Monad (DiscoveryT arch m)

instance Monad m => MonadDiscoveryTrace arch (DiscoveryT arch m) where
  emitDiscoveryTraces tr = DiscoveryT $ tell tr
  withDiscoveryTracing d (DiscoveryT f) = do
    (a, tr) <- DiscoveryT $ censor (\_ -> []) $ listen f
    emitDiscoveryTrace (NestedTraceData d tr)
    return a

type DiscoveryM arch = DiscoveryT arch Identity

emitDiscoveryTrace :: forall arch ids s m. HasCallStack => MonadDiscoveryTrace arch m => DiscoveryTraceData arch ids s -> m ()
emitDiscoveryTrace d = emitDiscoveryTraces [discoveryTrace d]

newtype DiscoveryST arch s m a = DiscoveryST { unDiscoveryST :: ReaderT (STL.STRef s [DiscoveryTrace arch]) m a }
  deriving (MonadTrans, Functor, Applicative)

deriving instance Monad m => Monad (DiscoveryST arch s m)

type DiscoverySTL arch s = DiscoveryST arch s (STL.ST s)
type DiscoverySTS arch s = DiscoveryST arch s (STS.ST s)
-- type DiscoveryM arch ids s m = DiscoveryT arch ids s (STS.ST s)

discoverySTStoSTL :: DiscoverySTS arch s a -> DiscoverySTL arch s a
discoverySTStoSTL (DiscoveryST f) = do
  r <- DiscoveryST $ ask
  DiscoveryST $ lift $ (STL.strictToLazyST (runReaderT f r))

discoverySTLtoSTS :: DiscoverySTL arch s a -> DiscoverySTS arch s a
discoverySTLtoSTS (DiscoveryST f) = do
  r <- DiscoveryST $ ask
  DiscoveryST $ lift $ (STL.lazyToStrictST (runReaderT f r))

instance MonadDiscoveryTrace arch (DiscoveryST arch s (STL.ST s)) where
    emitDiscoveryTraces [] = return ()
    emitDiscoveryTraces tr = DiscoveryST $ ask >>= \r -> lift $ STL.modifySTRef r (\traces -> tr ++ traces)
    withDiscoveryTracing d f = do
      r <- DiscoveryST $ ask
      oldTraces <- lift $ STL.readSTRef r
      a <- f
      nextTraces <- lift $ STL.readSTRef r
      -- take the prefix of new traces
      let (newTraces, _) = splitAt (length nextTraces - length oldTraces) nextTraces
      -- discard changes from the sub-computation
      lift $ STL.writeSTRef r oldTraces
      emitDiscoveryTrace (NestedTraceData d newTraces)
      return a




instance MonadDiscoveryTrace arch (DiscoveryST arch s (STS.ST s)) where
    emitDiscoveryTraces [] = return ()
    emitDiscoveryTraces tr = DiscoveryST $ ask >>= \r -> lift $ STS.modifySTRef r (\traces -> tr ++ traces)
    withDiscoveryTracing d f = do
      r <- DiscoveryST $ ask
      oldTraces <- lift $ STS.readSTRef r
      a <- f
      nextTraces <- lift $ STS.readSTRef r
      -- take the prefix of new traces
      let (newTraces, _) = splitAt (length nextTraces - length oldTraces) nextTraces
      lift $ STS.writeSTRef r oldTraces
      emitDiscoveryTrace (NestedTraceData d newTraces)
      return a

runDiscoverySTL :: DiscoverySTL arch s a -> STL.ST s (a, [DiscoveryTrace arch])
runDiscoverySTL f = do
  r <- STL.newSTRef []
  a <- runReaderT (unDiscoveryST f) r
  traces <- STL.readSTRef r
  return (a, traces)

runDiscoverySTS :: DiscoverySTS arch s a -> STS.ST s (a, [DiscoveryTrace arch])
runDiscoverySTS f = do
  r <- STS.newSTRef []
  a <- runReaderT (unDiscoveryST f) r
  traces <- STS.readSTRef r
  return (a, traces)

newtype DiscoveryTraceT arch m a = DiscoveryTraceT { _unDiscoveryTraceT :: WriterT [DiscoveryTrace arch] m a }
  deriving (Functor, Applicative, Monad)

runDiscoveryTraceT :: DiscoveryTraceT arch m a -> m (a, [DiscoveryTrace arch])
runDiscoveryTraceT (DiscoveryTraceT f) = runWriterT f