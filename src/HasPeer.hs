{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module HasPeer where

import Control.Carrier.Lift
import Control.Carrier.Random.Gen
import Control.Carrier.Reader
import Control.Carrier.State.Church hiding (get)
import qualified Control.Carrier.State.Strict as S
import Control.Effect.Labelled
import Control.Monad (forM, forM_, forever, void)
import Control.Monad.Class.MonadFork
import Control.Monad.Class.MonadSTM
import Control.Monad.Class.MonadSay
import Control.Monad.Class.MonadTime
import Control.Monad.Class.MonadTimer
import Control.Monad.IO.Class
import Control.Monad.IOSim (ppEvents, ppTrace, runSimTrace, selectTraceEventsSay)
import Data.Kind
import Data.Map (Map)
import qualified Data.Map as Map
import GHC.TypeLits
import qualified HasServer as HS
import Method
import Sum
import System.Random (mkStdGen)
import Type

newtype NodeID = NodeID Int deriving (Show, Eq, Ord)

type HasPeer (serverName :: Symbol) api n sig m =
  ( HasLabelled serverName (Peer n api) sig m,
    Has (Lift n) sig m
  )

data PeerState n ms = PeerState
  { nodeID :: NodeID,
    nodeQueue :: TQueue n (Sum ms n),
    peersQueue :: Map NodeID (TQueue n (Sum ms n))
  }

type Peer :: (Type -> Type) -> [(Type -> Type) -> Type] -> (Type -> Type) -> Type -> Type
data Peer n ms m a where
  RGetSelfQueue :: Peer n ms m (TQueue n (Sum ms n))
  RGetSelfNodeID :: Peer n ms m NodeID
  --------------------------------------------------------------------
  RCall :: SCall t req resp :< ms => NodeID -> (Call req resp -> t) -> req -> Peer n ms m resp
  RCast :: SCast t msg :< ms => NodeID -> (Cast msg -> t) -> msg -> Peer n ms m ()
  RGet :: SGet t resp :< ms => NodeID -> (Get resp -> t) -> Peer n ms m resp
  RCallAll ::
    SCall t req resp :< ms =>
    (Call req resp -> t) ->
    req ->
    Peer n ms m [(NodeID, TMVar n resp)]
  RCastAll :: SCast t msg :< ms => (Cast msg -> t) -> msg -> Peer n ms m ()
  RGetAll :: SGet t resp :< ms => (Get resp -> t) -> Peer n ms m [(NodeID, TMVar n resp)]

getSelfNodeID ::
  forall (s :: Symbol) n ms sig m.
  ( HasLabelled s (Peer n ms) sig m
  ) =>
  m NodeID
getSelfNodeID = sendLabelled @s RGetSelfNodeID
{-# INLINE getSelfNodeID #-}

getSelfQueue ::
  forall (s :: Symbol) n ms sig m.
  ( HasLabelled s (Peer n ms) sig m
  ) =>
  m (TQueue n (Sum ms n))
getSelfQueue = sendLabelled @s RGetSelfQueue
{-# INLINE getSelfQueue #-}

getAll ::
  forall (s :: Symbol) n ms sig m resp t.
  ( HasLabelled s (Peer n ms) sig m,
    SGet t resp :< ms
  ) =>
  (Get resp -> t) ->
  m [(NodeID, TMVar n resp)]
getAll t = sendLabelled @s (RGetAll t)
{-# INLINE getAll #-}

callAll ::
  forall (s :: Symbol) n ms sig m req resp t.
  ( HasLabelled s (Peer n ms) sig m,
    SCall t req resp :< ms
  ) =>
  (Call req resp -> t) ->
  req ->
  m [(NodeID, TMVar n resp)]
callAll t req = sendLabelled @s (RCallAll t req)
{-# INLINE callAll #-}

castAll ::
  forall (s :: Symbol) n ms sig m msg t.
  ( HasLabelled s (Peer n ms) sig m,
    SCast t msg :< ms
  ) =>
  (Cast msg -> t) ->
  msg ->
  m ()
castAll t msg = sendLabelled @s (RCastAll t msg)
{-# INLINE castAll #-}

call ::
  forall (s :: Symbol) n ms sig m req resp t.
  ( HasLabelled s (Peer n ms) sig m,
    SCall t req resp :< ms
  ) =>
  NodeID ->
  (Call req resp -> t) ->
  req ->
  m resp
call nid t req = sendLabelled @s (RCall nid t req)
{-# INLINE call #-}

cast ::
  forall (s :: Symbol) n ms sig m msg t.
  ( HasLabelled s (Peer n ms) sig m,
    SCast t msg :< ms
  ) =>
  NodeID ->
  (Cast msg -> t) ->
  msg ->
  m ()
cast nid t msg = sendLabelled @s (RCast nid t msg)
{-# INLINE cast #-}

get ::
  forall (s :: Symbol) n ms sig m resp t.
  ( HasLabelled s (Peer n ms) sig m,
    SGet t resp :< ms
  ) =>
  NodeID ->
  (Get resp -> t) ->
  m resp
get nid t = sendLabelled @s (RGet nid t)
{-# INLINE get #-}

newtype PeerC n ms m a = PeerC {unPeerC :: StateC (PeerState n ms) m a}
  deriving (Functor, Applicative, Monad, MonadIO)

instance
  (MonadSTM n, Has (Lift n) sig m) =>
  Algebra (Peer n ms :+: sig) (PeerC n ms m)
  where
  alg hdl sig ctx = PeerC $ case sig of
    L (RCall nid (_ :: Call req resp -> t) req) -> StateC $ \k ps@PeerState {peersQueue} -> do
      case Map.lookup nid peersQueue of
        Nothing -> k ps (error "node id not exist" <$ ctx)
        Just tq -> do
          resp <- sendM @n $ do
            tmvar <- newEmptyTMVarIO
            atomically $ writeTQueue tq (inject $ SCall @t @req @resp req tmvar)
            atomically $ takeTMVar tmvar
          k ps (resp <$ ctx)
    L (RCast nid (_ :: Cast msg -> t) msg) -> StateC $ \k ps@PeerState {peersQueue} -> do
      case Map.lookup nid peersQueue of
        Nothing -> k ps (error "node id not exist" <$ ctx)
        Just tq -> do
          sendM @n $ do
            atomically $ writeTQueue tq (inject $ SCast @t @msg msg)
          k ps ctx
    L (RGet nid (_ :: Get resp -> t)) -> StateC $ \k ps@PeerState {peersQueue} -> do
      case Map.lookup nid peersQueue of
        Nothing -> k ps (error "node id not exist" <$ ctx)
        Just tq -> do
          resp <- sendM @n $ do
            tmvar <- newEmptyTMVarIO
            atomically $ writeTQueue tq (inject $ SGet @t @resp tmvar)
            atomically $ takeTMVar tmvar
          k ps (resp <$ ctx)
    L (RCallAll (_ :: Call req resp -> t) req) -> StateC $ \k ps@PeerState {peersQueue} -> do
      pars <- forM (Map.toList peersQueue) $ \(idx, tq) -> sendM @n $ do
        tmvar <- newEmptyTMVarIO
        atomically $ writeTQueue tq (inject $ SCall @t @req @resp req tmvar)
        pure (idx, tmvar)
      k ps (pars <$ ctx)
    L (RCastAll (_ :: Cast msg -> t) msg) -> StateC $ \k ps@PeerState {peersQueue} -> do
      Map.traverseWithKey
        (\_ tq -> sendM @n $ atomically $ writeTQueue tq (inject $ SCast @t @msg msg))
        peersQueue
      k ps ctx
    L (RGetAll (_ :: Get resp -> t)) -> StateC $ \k ps@PeerState {peersQueue} -> do
      pars <- forM (Map.toList peersQueue) $ \(idx, tq) -> sendM @n $ do
        tmvar <- newEmptyTMVarIO
        atomically $ writeTQueue tq (inject $ SGet @t @resp tmvar)
        pure (idx, tmvar)
      k ps (pars <$ ctx)
    L RGetSelfQueue -> StateC $ \k ps@PeerState {nodeQueue} ->
      k ps (nodeQueue <$ ctx)
    L RGetSelfNodeID -> StateC $ \k ps@PeerState {nodeID} ->
      k ps (nodeID <$ ctx)
    R signa -> alg (unPeerC . hdl) (R signa) ctx
  {-# INLINE alg #-}

runWithPeers ::
  forall (name :: Symbol) m n ms a.
  Applicative m =>
  PeerState n ms ->
  Labelled name (PeerC n ms) m a ->
  m (PeerState n ms, a)
runWithPeers ps = runState (curry pure) ps . unPeerC . runLabelled
{-# INLINE runWithPeers #-}

------------- example

----- counter server

data AddCounter where
  AddCounter :: Cast () -> AddCounter

data GetCounter where
  GetCounter :: Get Int -> GetCounter

type CounterApi = '[K 'AddCounter, K 'GetCounter]

class CHandler n a where
  chandler :: (Has (State Int) sig m, Has (Lift n) sig m, MonadSTM n) => a n -> m ()

instance CHandler n (SCast AddCounter ()) where
  chandler (SCast _) = modify @Int (+ 1)

instance CHandler n (SGet GetCounter Int) where
  chandler (SGet tmvar) = do
    i <- S.get
    S.put (0 :: Int)
    sendM @n $ atomically $ putTMVar tmvar i

counterServer ::
  forall n sig m.
  ( Has (State Int) sig m,
    Has (Lift n) sig m,
    MonadSTM n
  ) =>
  TQueue n (Sum CounterApi n) ->
  m ()
counterServer tq = forever $ do
  sv <- sendM @n $ atomically $ readTQueue tq
  apply @(CHandler n) chandler sv

counterClient ::
  forall n sig m.
  ( HS.HasServer "c" CounterApi '[GetCounter] n sig m,
    MonadDelay n,
    MonadSay n
  ) =>
  m ()
counterClient = forever $ do
  sendM @n $ threadDelay 1
  i <- HS.get @"c" GetCounter
  sendM @n $ say $ show i

-------------------------------------------------------------

data Role = Master | Slave deriving (Show)

data ChangeMaster where
  ChangeMaster :: Get () -> ChangeMaster

data GetMsg where
  GetMsg :: Get Int -> GetMsg

type Api = '[K 'ChangeMaster, K 'GetMsg]

t1 ::
  forall n sig m.
  ( Has (S.State Role :+: Random :+: Reader (TVar n Int)) sig m,
    HS.HasServer "c" CounterApi '[AddCounter] n sig m,
    HasPeer "m" Api n sig m,
    MonadTime n,
    MonadDelay n,
    MonadSay n,
    MonadSTM n
  ) =>
  m ()
t1 = forever $ do
  S.get @Role >>= \case
    Master -> do
      res <- getAll @"m" GetMsg
      vals <- forM res $ \(a, b) -> do
        val <- sendM @n $ atomically $ readTMVar b
        pure (val, a)
      let mnid = snd $ maximum vals
      get @"m" mnid ChangeMaster
      put Slave
    Slave -> do
      tq <- getSelfQueue @"m"
      sv <- sendM @n $ atomically $ readTQueue tq
      apply @(HandlerM n) handlerM sv

class HandlerM n a where
  handlerM ::
    ( Has (S.State Role :+: Random :+: Reader (TVar n Int)) sig m,
      HS.HasServer "c" CounterApi '[AddCounter] n sig m,
      MonadSTM n,
      MonadDelay n,
      MonadTime n,
      MonadSay n,
      HasPeer "m" Api n sig m
    ) =>
    a n ->
    m ()

instance HandlerM n (SGet ChangeMaster ()) where
  handlerM (SGet tmvar) = do
    put Master
    HS.cast @"c" AddCounter ()
    sendM @n $ do
      atomically $ putTMVar tmvar ()
  {-# INLINE handlerM #-}

instance HandlerM n (SGet GetMsg Int) where
  handlerM (SGet tmvar) = do
    i <- uniformR (1, 100000)
    sendM @n $ atomically $ putTMVar tmvar i
  {-# INLINE handlerM #-}

r0 ::
  forall n.
  ( MonadSTM n,
    MonadDelay n,
    MonadTime n,
    MonadFork n,
    Algebra (Lift n) n,
    MonadSay n
  ) =>
  n ()
r0 = do
  counterChan <- newTQueueIO @_ @(Sum CounterApi n)

  forkIO $ void $ S.runState @Int 0 $ counterServer counterChan

  nodes <- forM [1 .. 4] $ \i -> do
    tc <- newTQueueIO @_ @(Sum Api n)
    pure (NodeID i, tc)
  let nodeMap = Map.fromList nodes
  res <- forM nodes $ \(nid, tc) -> do
    pure (PeerState nid tc (Map.delete nid nodeMap))

  counterTVar <- newTVarIO @_ @Int 0
  case res of
    (h : hs) -> do
      forkIO $
        void $
          runWithPeers @"m" h $
            HS.runWithServer @"c" counterChan $
              runRandom (mkStdGen 1) $ S.runState Master $ runReader counterTVar t1
      forM_ (zip [10 ..] hs) $ \(i, h') -> do
        forkIO $
          void $
            runWithPeers @"m" h' $
              HS.runWithServer @"c" counterChan $
                runRandom (mkStdGen (2)) $ S.runState Slave $ runReader counterTVar t1
    _ -> error "nice"

  void $ HS.runWithServer @"c" counterChan counterClient

-- >>> res
res = writeFile "peer.log" $ unlines $ selectTraceEventsSay $ runSimTrace r0
