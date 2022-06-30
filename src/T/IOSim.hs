{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module T.IOSim where

import Control.Algebra
-- import Control.Concurrent

import Control.Carrier.Lift
import Control.Carrier.Random.Gen
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Effect.Labelled (HasLabelled, Labelled, runLabelled, sendLabelled)
import Control.Monad
import Control.Monad.Class.MonadFork
import Control.Monad.Class.MonadSTM
import Control.Monad.Class.MonadSay
import Control.Monad.IO.Class
import Control.Monad.IOSim (runSimTrace, selectTraceEventsSay)
import Control.Monad.IOSim.Types hiding (Labelled, TVar)
import Control.Tracer
import Data.IORef
import Data.Kind
import GHC.TypeLits
import Sum1
import System.Random (mkStdGen)
import T.HasServer
import T.IO (client, server)
import TS1

------------------------------------------------------------------
newtype ClientCallC s r m a = ClientCallC
  { unClientCallC ::
      ReaderC
        ( TQueue (IOSim s) (Sum (TReq r), TMVar (IOSim s) (Sum (TResp r))),
          TMVar (IOSim s) (Sum (TResp r))
        )
        m
        a
  }
  deriving (Functor, Applicative, Monad, MonadIO)

instance
  ( Algebra sig m,
    Has (Lift (IOSim s)) sig m
  ) =>
  Algebra (ClientCall r :+: sig) (ClientCallC s r m)
  where
  alg hdl sig ctx = ClientCallC $
    ReaderC $ \(chan, mvar) -> case sig of
      L (ClientCall (_ :: Call req resp -> t) req) -> do
        res <- sendM @(IOSim s) $ do
          atomically $ writeTQueue chan (inject (Req @t req), mvar)
          project @(Resp t resp) <$> atomically (takeTMVar mvar)
        case res of
          Nothing -> error "DO NOT HAPPEN"
          Just (Resp r) -> pure (r <$ ctx)
      R signa -> alg (runReader (chan, mvar) . unClientCallC . hdl) signa ctx

runSupportCall ::
  forall (name :: Symbol) s r m a sig.
  Has (Lift (IOSim s)) sig m =>
  TQueue (IOSim s) (Sum (TReq r), TMVar (IOSim s) (Sum (TResp r))) ->
  Labelled name (ClientCallC s r) m a ->
  m a
runSupportCall chan f = do
  mvar <- sendM @(IOSim s) newEmptyTMVarIO
  runReader (chan, mvar) . unClientCallC @s @r $ runLabelled f

------------------------------------------------------------------

newtype ServerCallC s r m a = ServerCallC
  { unServerCallC ::
      ReaderC
        ( TQueue (IOSim s) (Sum (TReq r), TMVar (IOSim s) (Sum (TResp r))),
          TVar (IOSim s) (TMVar (IOSim s) (Sum (TResp r)))
        )
        m
        a
  }
  deriving (Functor, Applicative, Monad, MonadIO)

instance
  ( Algebra sig m,
    Has (Lift (IOSim s)) sig m
  ) =>
  Algebra (ServerCall r :+: sig) (ServerCallC s r m)
  where
  alg hdl sig ctx = ServerCallC $
    ReaderC $ \(chan, ref) -> case sig of
      L ServerGet -> do
        (sv, mvar) <- sendM @(IOSim s) $ atomically $ readTQueue chan
        sendM @(IOSim s) $ atomically $ writeTVar ref mvar
        pure (sv <$ ctx)
      L (ServerPut s) -> do
        sendM @(IOSim s) $ do
          mvar <- readTVarIO ref
          atomically $ putTMVar mvar s
        pure ctx
      R signa -> alg (runReader (chan, ref) . unServerCallC . hdl) signa ctx

runSupportHandleCall ::
  forall (name :: Symbol) s r m a sig.
  Has (Lift (IOSim s)) sig m =>
  TQueue (IOSim s) (Sum (TReq r), TMVar (IOSim s) (Sum (TResp r))) ->
  Labelled name (ServerCallC s r) m a ->
  m a
runSupportHandleCall chan f = do
  ref <- sendM @(IOSim s) $ newTVarIO undefined
  runReader (chan, ref) . unServerCallC @s @r $ runLabelled f

-- ------------------------------------------------------------------

instance Algebra (Lift (IOSim s)) (IOSim s) where
  alg hdl (LiftWith with) = with hdl
  {-# INLINE alg #-}

sayTracer :: forall s sig m a. (Has (Lift (IOSim s)) sig m, Show a) => Tracer m a
sayTracer = Tracer $ \v -> sendM @(IOSim s) (say $ show v)

r :: forall s. IOSim s ()
r = do
  chan <- newTQueueIO
  forkIO $ void $ runSupportHandleCall @"a1" @s chan (server @Int (sayTracer @s))
  void $ runSupportCall @"a1" @s chan $ runReader @Int 1 (client @Int (sayTracer @s))

-- >>> runR
runR = writeFile "res" $ unlines $ selectTraceEventsSay $ runSimTrace r
