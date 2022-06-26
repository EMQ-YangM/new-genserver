{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module T3 where

import Codec.CBOR.Decoding
import Codec.CBOR.Encoding
import Codec.Serialise
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
import Data.Kind
import Data.Time (UTCTime)
import GHC.Base
import GHC.TypeLits
import S
import Unsafe.Coerce (unsafeCoerce)

type Sum :: [(Type -> Type) -> Type] -> (Type -> Type) -> Type
data Sum r n where
  Sum :: Int -> t n -> Sum r n

type family
  ElemIndex
    (t :: (Type -> Type) -> Type)
    (ts :: [(Type -> Type) -> Type]) ::
    Nat
  where
  ElemIndex t0 ('(:) t0 _) = 0
  ElemIndex t1 ('(:) t0 ('(:) t1 _)) = 1
  ElemIndex t2 ('(:) t0 ('(:) t1 ('(:) t2 _))) = 2
  ElemIndex t3 ('(:) t0 ('(:) t1 ('(:) t2 ('(:) t3 _)))) = 3

type Element t r = KnownNat (ElemIndex t r)

type t :< r = Element t r

newtype P (t :: (Type -> Type) -> Type) (r :: [(Type -> Type) -> Type]) = P {unP :: Int}

elemNo :: forall t r. (t :< r) => P t r
elemNo = P (fromIntegral (natVal' (proxy# :: Proxy# (ElemIndex t r))))

unsafeInject :: Int -> t n -> Sum r n
unsafeInject = Sum

inject :: forall e r n. (e :< r) => e n -> Sum r n
inject = unsafeInject (unP (elemNo :: P e r))

class
  Apply
    (c :: ((Type -> Type) -> Type) -> Constraint)
    (fs :: [(Type -> Type) -> Type])
  where
  apply :: (forall g. c g => g n -> b) -> Sum fs n -> b

instance constraint g0 => Apply constraint '[g0] where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0 n)

instance
  ( constraint g0,
    constraint g1
  ) =>
  Apply constraint '[g0, g1]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0 n)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1 n)

instance
  ( constraint g0,
    constraint g1,
    constraint g2
  ) =>
  Apply constraint '[g0, g1, g2]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0 n)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1 n)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2 n)

instance
  ( constraint g0,
    constraint g1,
    constraint g2,
    constraint g3
  ) =>
  Apply constraint '[g0, g1, g2, g3]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0 n)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1 n)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2 n)
  apply f (Sum 3 r) = f (unsafeCoerce r :: g3 n)

class ShowT (v :: (Type -> Type) -> Type) where
  showT :: v n -> String

instance Apply ShowT r => ShowT (Sum r) where
  showT s@(Sum i _) = "Sum " ++ show i ++ " " ++ apply @ShowT showT s

instance ShowT (SGet a resp) where
  showT (SGet _) = "SGet"

instance Show msg => ShowT (SCast a msg) where
  showT (SCast msg) = "SCast msg is" ++ show msg

instance Show req => ShowT (SCall a req resp) where
  showT (SCall req _) = "SCall req is " ++ show req

instance ShowT (Sum r) => Show (Sum r n) where
  show = showT

-------------------------------------------------
newtype SGet a resp n = SGet (TMVar n resp)

type SCast :: Type -> Type -> (Type -> Type) -> Type
newtype SCast a msg n = SCast msg

data SCall a req resp n = SCall req (TMVar n resp)

data MethodTracer
  = CallSenderSendReq UTCTime
  | CallSenderRecvAndDecodeSuccess UTCTime
  | CallRecverRecvReqSuccess UTCTime
  | CallRecverInjectSCallToChan UTCTime
  | CallRecverRespFromUpLevelApp UTCTime
  | CallRecverSendRespBack UTCTime
  | CastSenderMsg UTCTime
  | CastRecverRecvMsgSuccess UTCTime
  | GetSenderRecvResponse UTCTime
  | GetSenderRecvResponseDecodeSuccess UTCTime
  | GetRecverInjectChan UTCTime
  | GetRecverGetUpLevelResp UTCTime
  | GetRecverSendRespBack UTCTime
  deriving (Show)

class
  SR1
    (n :: Type -> Type)
    (r :: [(Type -> Type) -> Type])
    (a :: (Type -> Type) -> Type)
  where
  sender ::
    Tracer n MethodTracer ->
    TVar n (Maybe LBS.ByteString) ->
    a n ->
    Channel n LBS.ByteString ->
    n ()

  recver ::
    Tracer n MethodTracer ->
    TVar n (Maybe LBS.ByteString) ->
    TQueue n (Sum r n) ->
    Channel n LBS.ByteString ->
    n ()

instance
  ( SCast a msg :< r,
    MonadST n,
    MonadTime n,
    MonadSTM n,
    Serialise msg
  ) =>
  SR1 n r (SCast a msg)
  where
  sender methodTracer _ (SCast msg) Channel {send} = do
    ct <- getCurrentTime
    traceWith methodTracer $ CastSenderMsg ct
    send $ convertCborEncoder encode msg

  recver methodTracer ref chan channel = do
    lbs <- readTVarIO ref
    vdec <- convertCborDecoder (decode @msg)
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        atomically $ writeTVar ref jl
        ct <- getCurrentTime
        traceWith methodTracer $ CastRecverRecvMsgSuccess ct
        atomically $ writeTQueue chan (inject (SCast @a v))

instance
  ( SGet a resp :< r,
    MonadST n,
    MonadTime n,
    MonadSTM n,
    Serialise resp
  ) =>
  SR1 n r (SGet a resp)
  where
  sender methodTracer ref (SGet mvar) channel = do
    lbs <- readTVarIO ref
    vdec <- convertCborDecoder decode
    ct <- getCurrentTime
    traceWith methodTracer $ GetSenderRecvResponse ct
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        ct <- getCurrentTime
        traceWith methodTracer $ GetSenderRecvResponseDecodeSuccess ct
        atomically $ writeTVar ref jl
        atomically $ putTMVar mvar v

  recver methodTracer _ chan Channel {send} = do
    mvar <- newEmptyTMVarIO @n @resp

    ct <- getCurrentTime
    traceWith methodTracer $ GetRecverInjectChan ct
    atomically $ writeTQueue chan (inject (SGet @a mvar))
    var <- atomically $ takeTMVar mvar
    ct <- getCurrentTime
    traceWith methodTracer $ GetRecverGetUpLevelResp ct
    send $ convertCborEncoder encode var
    ct <- getCurrentTime
    traceWith methodTracer $ GetRecverSendRespBack ct

instance
  ( SCall a req resp :< r,
    MonadSTM n,
    MonadST n,
    MonadTime n,
    Serialise resp,
    Serialise req
  ) =>
  SR1 n r (SCall a req resp)
  where
  sender methodTracer ref (SCall req tmvar) channel@Channel {send} = do
    lbs <- readTVarIO ref
    ct <- getCurrentTime
    traceWith methodTracer $ CallSenderSendReq ct
    send $ convertCborEncoder encode req
    vdec <- convertCborDecoder decode
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        atomically $ writeTVar ref jl
        ct <- getCurrentTime
        traceWith methodTracer $ CallSenderRecvAndDecodeSuccess ct
        atomically $ putTMVar tmvar v

  recver methodTracer ref chan channel@Channel {send} = do
    lbs <- readTVarIO ref
    vdec <- convertCborDecoder (decode @req)
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        ct <- getCurrentTime
        traceWith methodTracer $ CallRecverRecvReqSuccess ct
        atomically $ writeTVar ref jl
        mvar <- newEmptyTMVarIO @n @resp
        ct <- getCurrentTime
        traceWith methodTracer $ CallRecverInjectSCallToChan ct
        atomically $ writeTQueue chan (inject (SCall @a v mvar))
        var <- atomically $ takeTMVar mvar
        ct <- getCurrentTime
        traceWith methodTracer $ CallRecverRespFromUpLevelApp ct
        send $ convertCborEncoder encode var
        ct <- getCurrentTime
        traceWith methodTracer $ CallRecverSendRespBack ct

data ClientTracer
  = ClientSendIndex Int UTCTime
  | ClientMethod MethodTracer
  deriving (Show)

clientHandler ::
  forall n r.
  ( Apply (SR1 n r) r,
    MonadTime n,
    MonadST n
  ) =>
  Tracer n ClientTracer ->
  Sum r n ->
  TVar n (Maybe LBS.ByteString) ->
  Channel n LBS.ByteString ->
  n ()
clientHandler clientTracer s@(Sum i _) ref channel@Channel {send} = do
  ct <- getCurrentTime
  traceWith clientTracer (ClientSendIndex i ct)
  send $ convertCborEncoder encodeInt i
  apply @(SR1 n r)
    ( \x ->
        sender @n @r
          (contramap ClientMethod clientTracer)
          ref
          x
          channel
    )
    s

data ServerTracer
  = ServerRecvIndexResult (Either DeserialiseFailure (Int, Maybe LBS.ByteString)) UTCTime
  | ServerMethod MethodTracer
  deriving (Show)

serverHandler ::
  forall n r.
  ( Apply (SR1 n r) r,
    MonadTime n,
    MonadSTM n,
    MonadST n
  ) =>
  Tracer n ServerTracer ->
  TVar n (Maybe LBS.ByteString) ->
  TQueue n (Sum r n) ->
  Channel n LBS.ByteString ->
  n ()
serverHandler serverTracer ref chan channel = do
  lbs <- readTVarIO ref
  vdec <- convertCborDecoder decodeInt
  val <- runDecoderWithChannel channel lbs vdec
  case val of
    Left e -> error (show e)
    Right (v, jl) -> do
      ct <- getCurrentTime
      traceWith serverTracer (ServerRecvIndexResult val ct)
      atomically $ writeTVar ref jl
      apply @(SR1 n r)
        ( \(_ :: k x) ->
            recver @n @r @k
              (contramap ServerMethod serverTracer)
              ref
              chan
              channel
        )
        (Sum v undefined :: Sum r n)

-------------------------------------------------
data A

data B

data C

data D

type Api n =
  Sum
    '[ SCall A Int Bool,
       SCall B () String,
       SCast C String,
       SGet D Int
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
  tmvar1 <- newEmptyTMVarIO @n @String
  atomically $ writeTQueue tq (inject $ SCall @B () tmvar1)
  tv1 <- atomically $ takeTMVar tmvar1
  say $ "client recv val: " ++ show tv1

  tmvar2 <- newEmptyTMVarIO @n @Bool
  atomically $ writeTQueue tq (inject $ SCall @A (1 :: Int) tmvar2)
  tv2 <- atomically $ takeTMVar tmvar2
  say $ "client recv val: " ++ show tv2

  replicateM_ 3 $ do
    atomically $ writeTQueue tq (inject $ SCast @C "wellcome")

  tmvar3 <- newEmptyTMVarIO @n @Int
  atomically $ writeTQueue tq (inject $ SGet @D tmvar3)
  tv3 <- atomically $ takeTMVar tmvar3
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
  handleM (SCall i tmvar) = do
    threadDelay 0.1
    atomically $ putTMVar tmvar True

instance HandleM (SCall B () String) where
  handleM (SCall i tmvar) = do
    atomically $ putTMVar tmvar "well"

instance HandleM (SCast C String) where
  handleM (SCast s) = say $ "server recv msg: " ++ s

instance HandleM (SGet D Int) where
  handleM (SGet tmvar) = do
    atomically $ putTMVar tmvar 10010

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
