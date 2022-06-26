{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Method where

import Codec.CBOR.Decoding
import Codec.CBOR.Write (toBuilder)
import Codec.Serialise
import Control.Monad.Class.MonadST
import Control.Monad.Class.MonadSTM
import Control.Monad.Class.MonadTime
import Control.Tracer
import qualified Data.ByteString.Lazy as LBS
import Data.Kind
import Serialise
import Sum

data Get resp

data Cast msg

data Call req resp

newtype SGet a resp n = SGet (TMVar n resp)

type SCast :: Type -> Type -> (Type -> Type) -> Type
newtype SCast a msg n = SCast msg

data SCall a req resp n = SCall req (TMVar n resp)

type family K a where
  K (a :: f -> b) = K1 b f

type family K1 a b where
  K1 b (Get resp) = SGet b resp
  K1 b (Cast msg) = SCast b msg
  K1 b (Call req resp) = SCall b req resp

instance ShowT (SGet a resp) where
  showT (SGet _) = "SGet"

instance Show msg => ShowT (SCast a msg) where
  showT (SCast msg) = "SCast msg is" ++ show msg

instance Show req => ShowT (SCall a req resp) where
  showT (SCall req _) = "SCall req is " ++ show req

instance ShowT (Sum r) => Show (Sum r n) where
  show = showT

data MethodTracer
  = CallSenderSendReq Time
  | CallSenderRecvAndDecodeSuccess Time
  | CallRecverRecvReqSuccess Time
  | CallRecverInjectSCallToChan Time
  | CallRecverRespFromUpLevelApp Time
  | CallRecverSendRespBack Time
  | CastSenderMsg Time
  | CastRecverRecvMsgSuccess Time
  | GetSenderRecvResponse Time
  | GetSenderRecvResponseDecodeSuccess Time
  | GetRecverInjectChan Time
  | GetRecverGetUpLevelResp Time
  | GetRecverSendRespBack Time
  deriving (Show)

class
  SR
    (n :: Type -> Type)
    (r :: [(Type -> Type) -> Type])
    (a :: (Type -> Type) -> Type)
  where
  sender ::
    Tracer n MethodTracer ->
    TVar n (Maybe LBS.ByteString) ->
    Int ->
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
  SR n r (SCast a msg)
  where
  sender methodTracer _ index (SCast msg) Channel {send} = do
    ct <- getMonotonicTime
    traceWith methodTracer $ CastSenderMsg ct
    send $ toLazyByteString (toBuilder $ encode index) <> convertCborEncoder encode msg

  recver methodTracer ref chan channel = do
    lbs <- readTVarIO ref
    vdec <- convertCborDecoder (decode @msg)
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        atomically $ writeTVar ref jl
        ct <- getMonotonicTime
        traceWith methodTracer $ CastRecverRecvMsgSuccess ct
        atomically $ writeTQueue chan (inject (SCast @a v))

instance
  ( SGet a resp :< r,
    MonadST n,
    MonadTime n,
    MonadSTM n,
    Serialise resp
  ) =>
  SR n r (SGet a resp)
  where
  sender methodTracer ref index (SGet mvar) channel@Channel {send} = do
    send $ toLazyByteString (toBuilder $ encode index)
    lbs <- readTVarIO ref
    vdec <- convertCborDecoder decode
    ct <- getMonotonicTime
    traceWith methodTracer $ GetSenderRecvResponse ct
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        ct <- getMonotonicTime
        traceWith methodTracer $ GetSenderRecvResponseDecodeSuccess ct
        atomically $ writeTVar ref jl
        atomically $ putTMVar mvar v

  recver methodTracer _ chan Channel {send} = do
    mvar <- newEmptyTMVarIO @n @resp
    ct <- getMonotonicTime
    traceWith methodTracer $ GetRecverInjectChan ct
    atomically $ writeTQueue chan (inject (SGet @a mvar))
    var <- atomically $ takeTMVar mvar
    ct <- getMonotonicTime
    traceWith methodTracer $ GetRecverGetUpLevelResp ct
    send $ convertCborEncoder encode var
    ct <- getMonotonicTime
    traceWith methodTracer $ GetRecverSendRespBack ct

instance
  ( SCall a req resp :< r,
    MonadSTM n,
    MonadST n,
    MonadTime n,
    Serialise resp,
    Serialise req
  ) =>
  SR n r (SCall a req resp)
  where
  sender methodTracer ref index (SCall req tmvar) channel@Channel {send} = do
    lbs <- readTVarIO ref
    ct <- getMonotonicTime
    traceWith methodTracer $ CallSenderSendReq ct
    send $ toLazyByteString (toBuilder $ encode index) <> convertCborEncoder encode req
    vdec <- convertCborDecoder decode
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        atomically $ writeTVar ref jl
        ct <- getMonotonicTime
        traceWith methodTracer $ CallSenderRecvAndDecodeSuccess ct
        atomically $ putTMVar tmvar v

  recver methodTracer ref chan channel@Channel {send} = do
    lbs <- readTVarIO ref
    vdec <- convertCborDecoder (decode @req)
    val <- runDecoderWithChannel channel lbs vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        ct <- getMonotonicTime
        traceWith methodTracer $ CallRecverRecvReqSuccess ct
        atomically $ writeTVar ref jl
        mvar <- newEmptyTMVarIO @n @resp
        ct <- getMonotonicTime
        traceWith methodTracer $ CallRecverInjectSCallToChan ct
        atomically $ writeTQueue chan (inject (SCall @a v mvar))
        var <- atomically $ takeTMVar mvar
        ct <- getMonotonicTime
        traceWith methodTracer $ CallRecverRespFromUpLevelApp ct
        send $ convertCborEncoder encode var
        ct <- getMonotonicTime
        traceWith methodTracer $ CallRecverSendRespBack ct

newtype ClientTracer
  = ClientMethod MethodTracer
  deriving (Show)

clientHandler ::
  forall n r.
  ( Apply (SR n r) r,
    MonadTime n,
    MonadST n
  ) =>
  Tracer n ClientTracer ->
  Sum r n ->
  TVar n (Maybe LBS.ByteString) ->
  Channel n LBS.ByteString ->
  n ()
clientHandler clientTracer s@(Sum i _) ref channel = do
  apply @(SR n r)
    ( \x ->
        sender @n @r
          (contramap ClientMethod clientTracer)
          ref
          i
          x
          channel
    )
    s

data ServerTracer
  = ServerRecvIndexResult (Either DeserialiseFailure (Int, Maybe LBS.ByteString)) Time
  | ServerMethod MethodTracer
  deriving (Show)

serverHandler ::
  forall n r.
  ( Apply (SR n r) r,
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
      ct <- getMonotonicTime
      traceWith serverTracer (ServerRecvIndexResult val ct)
      atomically $ writeTVar ref jl
      apply @(SR n r)
        ( \(_ :: k x) ->
            recver @n @r @k
              (contramap ServerMethod serverTracer)
              ref
              chan
              channel
        )
        (Sum v undefined :: Sum r n)
