{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module T2 where

import Control.Algebra
import Control.Carrier.Lift
import Control.Carrier.Random.Gen (Random, runRandom, uniformR)
import Control.Carrier.State.Strict
-- import Control.Concurrent
import Control.Monad
import Control.Monad.Class.MonadFork
import Control.Monad.Class.MonadSTM
import Control.Monad.Class.MonadSay
import Control.Monad.Class.MonadTimer
import Control.Monad.IO.Class
import Data.IORef
import Data.Kind
import Data.Map (Map)
import qualified Data.Map as Map
import System.Random (mkStdGen)

newtype NodeID = NodeID Int deriving (Show, Eq, Ord)

data Role = Master | Slave

data Msg n where
  ChangeMaster :: TMVar n () -> Msg n
  GetInt :: TMVar n Int -> Msg n

data PeerState n = PeerState
  { nodeID :: NodeID,
    nodeRole :: Role,
    nodeQueue :: TQueue n (Msg n),
    peersQueue :: Map NodeID (TQueue n (Msg n))
  }

t1 ::
  forall n sig m.
  ( Has (State (PeerState n) :+: Random :+: Lift n) sig m,
    MonadSTM n
  ) =>
  TVar n Int ->
  m ()
t1 counter = forever $ do
  gets @(PeerState n) nodeRole >>= \case
    Master -> do
      psq <- gets @(PeerState n) peersQueue
      vals <- forM (Map.toList psq) $ \(idx, tq) -> do
        mvar <- sendM @n newEmptyTMVarIO
        sendM @n $ atomically $ writeTQueue tq (GetInt mvar)
        val <- sendM @n $ atomically $ takeTMVar mvar
        pure (val, idx)
      let mnid = snd $ maximum vals
      case Map.lookup mnid psq of
        Nothing -> undefined
        Just tq -> do
          mvar <- sendM @n newEmptyTMVarIO
          sendM @n $ atomically $ writeTQueue tq (ChangeMaster mvar)
          sendM @n $ atomically $ takeTMVar mvar
          modify @(PeerState n) (\pp -> pp {nodeRole = Slave})
    Slave -> do
      tq <- gets @(PeerState n) nodeQueue
      sv <- sendM @n $ atomically $ readTQueue tq
      case sv of
        ChangeMaster mvar -> do
          modify @(PeerState n) (\pp -> pp {nodeRole = Master})
          sendM @n $ atomically $ modifyTVar' counter (\(!x) -> x + 1)
          sendM @n $ atomically $ putTMVar mvar ()
        GetInt mvar -> do
          i <- uniformR (1, 100000)
          sendM @n $ atomically $ putTMVar mvar i

r :: forall n. (MonadSTM n, MonadDelay n, MonadFork n, MonadFail n, Algebra (Lift n) n, MonadSay n) => n ()
r = do
  counterRef <- newTVarIO 0

  nodes <- forM [1 .. 4] $ \i -> do
    tq <- newTQueueIO @n @(Msg n)
    pure (NodeID i, tq)
  let nodeMap = Map.fromList nodes
  (h : hs) <- forM nodes $ \(nid, tq) -> do
    pure (PeerState nid Slave tq (Map.delete nid nodeMap))

  let h1 = h {nodeRole = Master}

  forkIO $ void $ runState @(PeerState n) h1 $ runRandom (mkStdGen 1) $ (t1 @n) counterRef

  forM_ hs $ \h' -> do
    forkIO $ void $ runState @(PeerState n) h' $ runRandom (mkStdGen 2) $ (t1 @n) counterRef

  forever $ do
    threadDelay 1
    counter <- readTVarIO counterRef
    atomically $ modifyTVar' counterRef (const 0)
    say $ show counter
