{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module T2 where

import Codec.CBOR.Decoding
import Codec.CBOR.Encoding
import Codec.Serialise
import Control.Concurrent
import Control.Monad
import qualified Data.ByteString.Lazy as LBS
import Data.IORef
import S
import T1

data Cast msg

data Get resp

data Call req resp

newtype SCast t msg = SCast msg

newtype SGet t resp = SGet (MVar resp)

data SCall t req resp = SCall req (MVar resp)

class SR1 r a where
  sender :: IORef (Maybe LBS.ByteString) -> a -> Channel IO LBS.ByteString -> IO ()
  recver :: IORef (Maybe LBS.ByteString) -> Chan (Sum r) -> Channel IO LBS.ByteString -> IO ()

instance (SCast t msg :< r, Serialise msg) => SR1 r (SCast t msg) where
  sender _ (SCast msg) Channel {send} = send $ convertCborEncoder encode msg

  recver ref chan channel = do
    lbs <- readIORef ref
    vdec <- convertCborDecoder (decode @msg)
    -- recv msg
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        writeIORef ref jl
        putStrLn "server decode msg success"
        writeChan chan (inject (SCast @t v))

instance (SGet t resp :< r, Serialise resp) => SR1 r (SGet t resp) where
  sender ref (SGet mvar) channel = do
    lbs <- readIORef ref
    vdec <- convertCborDecoder decode
    -- recv resp
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        writeIORef ref jl
        putMVar mvar v

  recver _ chan Channel {send} = do
    mvar <- newEmptyMVar @resp
    writeChan chan (inject (SGet @t mvar))
    var <- takeMVar mvar
    send $ convertCborEncoder encode var

instance (SCall t req resp :< r, Serialise req, Serialise resp) => SR1 r (SCall t req resp) where
  sender ref (SCall req mvar) channel@Channel {send} = do
    lbs <- readIORef ref
    -- send req
    send $ convertCborEncoder encode req
    vdec <- convertCborDecoder decode
    -- recv resp
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        writeIORef ref jl
        -- put resp to mvar
        putMVar mvar v

  recver ref chan channel@Channel {send} = do
    lbs <- readIORef ref
    vdec <- convertCborDecoder (decode @req)
    -- recv req
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        putStrLn "server decode req success"
        writeIORef ref jl
        mvar <- newEmptyMVar @resp
        -- write SCall to chan
        writeChan chan (inject (SCall @t v mvar))
        -- take mvar, wait resp
        var <- takeMVar mvar
        -- resp for req
        send $ convertCborEncoder encode var

clientHandler ::
  forall r.
  Apply (SR1 r) r =>
  Sum r ->
  IORef (Maybe LBS.ByteString) ->
  Channel IO LBS.ByteString ->
  IO ()
clientHandler s@(Sum i _) ref channel@Channel {send} = do
  send $ convertCborEncoder encodeInt i
  apply @(SR1 r) (\x -> sender @r ref x channel) s

serverHandler ::
  forall r.
  (Apply (SR1 r) r) =>
  IORef (Maybe LBS.ByteString) ->
  Chan (Sum r) ->
  Channel IO LBS.ByteString ->
  IO ()
serverHandler ref chan channel = do
  lbs <- readIORef ref
  vdec <- convertCborDecoder decodeInt
  val <- runDecoderWithChannel channel lbs vdec
  case val of
    Left e -> error (show e)
    Right (v, jl) -> do
      writeIORef ref jl
      apply @(SR1 r)
        (\(_ :: k) -> recver @r @k ref chan channel)
        (Sum v undefined :: Sum r)

-------------------------- ee
data A

type F =
  Sum
    '[ SCall A Int Bool,
       SCall A Int Int,
       SCast A String,
       SGet A Int
     ]

client :: Chan F -> IO ()
client chan = do
  mvar <- newEmptyMVar @Bool
  putStrLn "client send req"
  writeChan chan (inject $ SCall @A (10 :: Int) mvar)
  resp <- takeMVar mvar
  putStrLn $ "client response val is " ++ show resp

  mvar <- newEmptyMVar @Int
  putStrLn "client send req"
  writeChan chan (inject $ SCall @A (11 :: Int) mvar)
  resp <- takeMVar mvar
  putStrLn $ "client response val is " ++ show resp

  writeChan chan (inject $ SCast @A "nice")
  mvar <- newEmptyMVar @Int
  writeChan chan (inject $ SGet @A mvar)
  tv <- takeMVar mvar
  putStrLn $ "get val is: " ++ show tv

clientLowHandler :: Chan F -> IORef (Maybe LBS.ByteString) -> Channel IO LBS.ByteString -> IO ()
clientLowHandler chan ref channel = forever $ do
  sv <- readChan chan
  clientHandler sv ref channel

-------------------------- ee

class HandleM a where
  handleM :: a -> IO ()

instance HandleM (SCall A Int Int) where
  handleM (SCall i mvar) = do
    putStrLn $ "server recv val " ++ show i
    putMVar mvar 10010
    putStrLn "server resp val 10010"

instance HandleM (SCall A Int Bool) where
  handleM (SCall i mvar) = do
    putStrLn $ "server recv val " ++ show i
    putMVar mvar True
    putStrLn "server resp val True"

instance HandleM (SCast A String) where
  handleM (SCast msg) = putStrLn $ "recv msg " ++ msg

instance HandleM (SGet A Int) where
  handleM (SGet mvar) = do
    putStrLn "recv get"
    putMVar mvar 111

server :: Chan F -> IO ()
server chan = forever $ do
  sv <- readChan chan
  apply @HandleM handleM sv

serverLowHandler :: Chan F -> IORef (Maybe LBS.ByteString) -> Channel IO LBS.ByteString -> IO ()
serverLowHandler chan ref channel = forever $ serverHandler ref chan channel

-------------------------- ee

example :: IO ()
example = do
  (clientChannel, serverChannel) <- createConnectedChannels
  ------------------------------------
  clientChan <- newChan
  clientRef <- newIORef Nothing
  forkIO $ void $ client clientChan
  forkIO $ void $ clientLowHandler clientChan clientRef clientChannel
  ------------------------------------
  serverChan <- newChan
  serverRef <- newIORef Nothing
  forkIO $ void $ server serverChan
  forkIO $ void $ serverLowHandler serverChan serverRef serverChannel
  threadDelay 1000

-------------------------- ee