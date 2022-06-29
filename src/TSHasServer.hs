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

module TSHasServer where

import Control.Algebra
import Control.Carrier.Random.Gen
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Concurrent
import Control.Effect.Labelled (HasLabelled, Labelled, runLabelled, sendLabelled)
import Control.Monad
import Control.Monad.IO.Class
import Data.IORef
import Data.Kind
import GHC.TypeLits
import Sum1
import System.Random (mkStdGen)
import TS1

------------------------------------------------------------------
data ClientCall (r :: [Type]) (m :: Type -> Type) (a :: Type) where
  ClientCall ::
    ( Req t req :< TReq r,
      Resp t resp :< TResp r
    ) =>
    (Call req resp -> t) ->
    req ->
    ClientCall r m resp

type SupportCall (name :: Symbol) r sig m =
  HasLabelled name (ClientCall r) sig m

call ::
  forall (name :: Symbol) r t req resp sig m.
  ( Req t req :< TReq r,
    Resp t resp :< TResp r,
    HasLabelled name (ClientCall r) sig m
  ) =>
  (Call req resp -> t) ->
  req ->
  m resp
call t req = sendLabelled @name (ClientCall t req)

------------------------------------------------------------------
newtype ClientCallC r m a = ClientCallC
  { unClientCallC ::
      ReaderC
        ( Chan (Sum (TReq r), MVar (Sum (TResp r))),
          MVar (Sum (TResp r))
        )
        m
        a
  }
  deriving (Functor, Applicative, Monad, MonadIO)

instance
  ( Algebra sig m,
    MonadIO m
  ) =>
  Algebra (ClientCall r :+: sig) (ClientCallC r m)
  where
  alg hdl sig ctx = ClientCallC $
    ReaderC $ \(chan, mvar) -> case sig of
      L (ClientCall (_ :: Call req resp -> t) req) -> do
        res <- liftIO $ do
          writeChan chan (inject (Req @t req), mvar)
          project @(Resp t resp) <$> takeMVar mvar
        case res of
          Nothing -> error "DO NOT HAPPEN"
          Just (Resp r) -> pure (r <$ ctx)
      R signa -> alg (runReader (chan, mvar) . unClientCallC . hdl) signa ctx

runSupportCall ::
  forall (name :: Symbol) r m a.
  (MonadIO m) =>
  Chan (Sum (TReq r), MVar (Sum (TResp r))) ->
  Labelled name (ClientCallC r) m a ->
  m a
runSupportCall chan f = do
  mvar <- liftIO newEmptyMVar
  runReader (chan, mvar) . unClientCallC @r $ runLabelled f

------------------------------------------------------------------
data ServerCall (r :: [Type]) (m :: Type -> Type) a where
  ServerGet :: ServerCall r m (Sum (TReq r))
  ServerPut :: Sum (TResp r) -> ServerCall r m ()

type SupportHandleCall (name :: Symbol) r sig m =
  ( HasLabelled name (ServerCall r) sig m,
    HandleCall r m
  )

serverHandleCall ::
  forall name r sig m.
  SupportHandleCall name r sig m =>
  HList (TMAP r m) ->
  m ()
serverHandleCall hl = do
  va <- sendLabelled @name ServerGet
  ha <- handleCall @r hl va
  sendLabelled @name (ServerPut ha)

newtype ServerCallC r m a = ServerCallC
  { unServerCallC ::
      ReaderC
        ( Chan (Sum (TReq r), MVar (Sum (TResp r))),
          IORef (MVar (Sum (TResp r)))
        )
        m
        a
  }
  deriving (Functor, Applicative, Monad, MonadIO)

instance
  ( Algebra sig m,
    MonadIO m
  ) =>
  Algebra (ServerCall r :+: sig) (ServerCallC r m)
  where
  alg hdl sig ctx = ServerCallC $
    ReaderC $ \(chan, ref) -> case sig of
      L ServerGet -> do
        (sv, mvar) <- liftIO $ readChan chan
        liftIO $ writeIORef ref mvar
        pure (sv <$ ctx)
      L (ServerPut s) -> do
        liftIO $ do
          mvar <- readIORef ref
          putMVar mvar s
        pure ctx
      R signa -> alg (runReader (chan, ref) . unServerCallC . hdl) signa ctx

runSupportHandleCall ::
  forall (name :: Symbol) r m a.
  (MonadIO m) =>
  Chan (Sum (TReq r), MVar (Sum (TResp r))) ->
  Labelled name (ServerCallC r) m a ->
  m a
runSupportHandleCall chan f = do
  ref <- liftIO $ newIORef undefined
  runReader (chan, ref) . unServerCallC @r $ runLabelled f

------------------------------------------------------------------
data A where
  A :: Call Int Bool -> A

data B where
  B :: Call Bool String -> B

data C where
  C :: Call Int Int -> C

data D a where
  D :: Call a Int -> D a

data E where
  E :: Call Int Bool -> E

data F where
  F :: Call () Int -> F

type Api a = [K 'A, K 'B, K 'C, K ('D @a), K 'E]

------------------------------------------------------------------
client ::
  forall a sig m.
  ( SupportCall "a1" (Api a) sig m,
    Has (Reader a) sig m,
    MonadIO m
  ) =>
  m ()
client = forever $ do
  val <- ask @a
  g <- call @"a1" D val
  liftIO $ print g

  g <- call @"a1" A 1
  liftIO $ print g

  g <- call @"a1" B True
  liftIO $ print g

------------------------------------------------------------------
server ::
  forall a sig m.
  ( SupportHandleCall "a1" (Api a) sig m,
    Show a,
    MonadIO m
  ) =>
  m ()
server = forever $ do
  serverHandleCall @"a1" $
    (\(Req i) -> do pure (Resp True))
      :| (\(Req i) -> pure (Resp "nice"))
      :| (\(Req i) -> pure (Resp i))
      :| (\(Req i) -> liftIO (print i) >> pure (Resp 1))
      :| (\(Req i) -> pure (Resp True))
      :| HNil

------------------------------------------

r :: IO ()
r = do
  chan <- newChan
  forkIO $ void $ runSupportHandleCall @"a1" chan (server @Int)
  void $ runSupportCall @"a1" chan $ runReader @Int 1 (client @Int)
