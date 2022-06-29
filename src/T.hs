{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

module T where

import Control.Algebra
import Control.Carrier.Random.Gen (Random, runRandom, uniformR)
import Control.Carrier.State.Strict
import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import System.Random (mkStdGen)

newtype NodeID = NodeID Int deriving (Show, Eq, Ord)

data Role = Master | Slave

data Msg where
  ChangeMaster :: MVar () -> Msg
  GetInt :: MVar Int -> Msg

data PeerState = PeerState
  { nodeID :: NodeID,
    nodeRole :: Role,
    nodeQueue :: Chan Msg,
    peersQueue :: Map NodeID (Chan Msg)
  }

t1 ::
  ( Has (State PeerState :+: Random) sig m,
    MonadIO m
  ) =>
  IORef Int ->
  m ()
t1 counter = forever $ do
  gets nodeRole >>= \case
    Master -> do
      psq <- gets peersQueue
      vals <- forM (Map.toList psq) $ \(idx, tq) -> do
        mvar <- liftIO newEmptyMVar
        liftIO $ writeChan tq (GetInt mvar)
        val <- liftIO $ takeMVar mvar
        pure (val, idx)
      let mnid = snd $ maximum vals
      case Map.lookup mnid psq of
        Nothing -> undefined
        Just tq -> do
          mvar <- liftIO newEmptyMVar
          liftIO $ writeChan tq (ChangeMaster mvar)
          liftIO $ takeMVar mvar
          modify (\pp -> pp {nodeRole = Slave})
    Slave -> do
      tq <- gets nodeQueue
      sv <- liftIO $ readChan tq
      case sv of
        ChangeMaster mvar -> do
          modify (\pp -> pp {nodeRole = Master})
          liftIO $ atomicModifyIORef' counter (\(!x) -> (x + 1, ()))
          liftIO $ putMVar mvar ()
        GetInt mvar -> do
          i <- uniformR (1, 100000)
          liftIO $ putMVar mvar i

r :: IO ()
r = do
  counterRef <- newIORef 0
  nodes <- forM [1 .. 4] $ \i -> do
    tq <- newChan
    pure (NodeID i, tq)
  let nodeMap = Map.fromList nodes
  (h : hs) <- forM nodes $ \(nid, tq) -> do
    pure (PeerState nid Slave tq (Map.delete nid nodeMap))

  let h1 = h {nodeRole = Master}

  forkIO $ void $ runState h1 $ runRandom (mkStdGen 1) $ t1 counterRef

  forM_ hs $ \h' -> do
    forkIO $ void $ runState h' $ runRandom (mkStdGen 2) $ t1 counterRef

  forever $ do
    threadDelay 1000000
    counter <- readIORef counterRef
    atomicModifyIORef' counterRef (const (0, ()))
    print counter
