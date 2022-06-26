{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Example where

import Control.Monad
import Control.Monad.Class.MonadFork
import Control.Monad.Class.MonadST
import Control.Monad.Class.MonadSTM
import Control.Monad.Class.MonadSay
import Control.Monad.Class.MonadTime
import Control.Monad.Class.MonadTimer
import Control.Monad.IOSim (ppTrace, runSimTrace, selectTraceEventsSay)
import Control.Tracer
import qualified Data.ByteString.Lazy as LBS
import Serialise
import Sum
import Method

get ::
  forall n resp a r.
  ( MonadSTM n,
    SGet a resp :< r
  ) =>
  TQueue n (Sum r n) ->
  (Get resp -> a) ->
  n resp
get tq _ = do
  tmvar <- newEmptyTMVarIO
  atomically $ writeTQueue tq $ inject $ SGet @a @resp @n tmvar
  atomically $ takeTMVar tmvar

cast ::
  forall n msg a r.
  ( MonadSTM n,
    SCast a msg :< r
  ) =>
  TQueue n (Sum r n) ->
  (Cast msg -> a) ->
  msg ->
  n ()
cast tq _ msg = do
  atomically $ writeTQueue tq $ inject $ SCast @a @msg @n msg

call ::
  forall n req resp a r.
  ( MonadSTM n,
    SCall a req resp :< r
  ) =>
  TQueue n (Sum r n) ->
  (Call req resp -> a) ->
  req ->
  n resp
call tq _ req = do
  tmvar <- newEmptyTMVarIO
  atomically $ writeTQueue tq $ inject $ SCall @a @req @resp @n req tmvar
  atomically $ takeTMVar tmvar

data A where
  A :: Call Int Bool -> A

data B where
  B :: Call () String -> B

data C where
  C :: Cast String -> C

data D where
  D :: Get Int -> D

type Api n =
  Sum
    '[ K 'A,
       K 'B,
       K 'C,
       K 'D
     ]
    n

client ::
  forall n.
  ( MonadSTM n,
    MonadSay n
  ) =>
  TQueue n (Api n) ->
  n ()
client tq = do
  tv1 <- call tq B ()
  say $ "client recv val: " ++ show tv1

  tv2 <- call tq A 1
  say $ "client recv val: " ++ show tv2

  replicateM_ 3 $ cast tq C "wellcome"

  tv3 <- get tq D
  say $ "client recv val: " ++ show tv3

clientLowHandler ::
  ( MonadSTM n,
    MonadTime n,
    MonadST n
  ) =>
  Tracer n ClientTracer ->
  TQueue n (Api n) ->
  TVar n (Maybe LBS.ByteString) ->
  Channel n LBS.ByteString ->
  n ()
clientLowHandler clientTracer chan ref channel = forever $ do
  sv <- atomically $ readTQueue chan
  clientHandler clientTracer sv ref channel

class HandleM a where
  handleM ::
    ( MonadSay n,
      MonadDelay n,
      MonadSTM n
    ) =>
    a n ->
    n ()

instance HandleM (SCall A Int Bool) where
  handleM (SCall _ tmvar) = do
    threadDelay 0.1
    atomically $ putTMVar tmvar True

instance HandleM (SCall B () String) where
  handleM (SCall _ tmvar) = atomically $ putTMVar tmvar "well"

instance HandleM (SCast C String) where
  handleM (SCast s) = say $ "server recv msg: " ++ s

instance HandleM (SGet D Int) where
  handleM (SGet tmvar) = atomically $ putTMVar tmvar 10010

server ::
  ( MonadSTM n,
    MonadSay n,
    MonadDelay n
  ) =>
  TQueue n (Api n) ->
  n ()
server tq = forever $ do
  sv <- atomically $ readTQueue tq
  apply @HandleM handleM sv

serverLowHandler ::
  ( MonadSTM n,
    MonadTime n,
    MonadST n
  ) =>
  Tracer n ServerTracer ->
  TQueue n (Api n) ->
  TVar n (Maybe LBS.ByteString) ->
  Channel n LBS.ByteString ->
  n ()
serverLowHandler serverTracer chan ref channel =
  forever $
    serverHandler serverTracer ref chan channel

example ::
  ( MonadSTM n,
    MonadFork n,
    MonadSay n,
    MonadDelay n,
    MonadST n,
    MonadTime n,
    MonadTimer n
  ) =>
  n ()
example = do
  (clientChannel, serverChannel) <- createConnectedChannels
  -- (clientChannel, serverChannel) <- createConnectedBufferedChannels 10
  ------------------------------------
  clientChan <- newTQueueIO
  clientRef <- newTVarIO Nothing
  forkIO (void $ client clientChan) >>= flip labelThread "client"
  forkIO (void $ clientLowHandler sayTracer clientChan clientRef clientChannel)
    >>= flip labelThread "client_low"
  ------------------------------------
  serverChan <- newTQueueIO
  serverRef <- newTVarIO Nothing
  forkIO (void $ server serverChan)
    >>= flip labelThread "server"
  let delayServerChannel = delayChannel 0.04 serverChannel
  forkIO (void $ serverLowHandler sayTracer serverChan serverRef delayServerChannel)
    >>= flip labelThread "server_low"
  threadDelay 10

sayTracer :: (MonadSay n, Show a) => Tracer n a
sayTracer = Tracer $ \v -> say (show v)

-- >>> res
res = do
  let resv = runSimTrace example
  writeFile "simEvents.log" $ ppTrace resv
  appendFile "simEvents.log" $ "\n\n" ++ unlines (selectTraceEventsSay resv)
