{-# LANGUAGE AllowAmbiguousTypes #-}
-- copy from: https://github.com/input-output-hk/typed-protocols
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module S where

import Codec.CBOR.Decoding
import qualified Codec.CBOR.Decoding as CBOR (Decoder)
import qualified Codec.CBOR.Encoding as CBOR (Encoding)
import Codec.CBOR.Pretty
import Codec.CBOR.Read (deserialiseFromBytes)
import qualified Codec.CBOR.Read as CBOR
import qualified Codec.CBOR.Write as CBOR
import Codec.Serialise
import Codec.Serialise.Encoding
import Control.Monad.Class.MonadST
import Control.Monad.Class.MonadSTM
import Control.Monad.Class.MonadSay
import Control.Monad.Class.MonadTimer
import Control.Monad.IOSim
import Control.Monad.ST
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BS
import qualified Data.ByteString.Builder.Extra as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Internal as LBS (smallChunkSize)
import Data.Data
import Data.Kind
import Data.Maybe (isNothing)
import GHC.TypeLits
import N2
import Test.QuickCheck (Arbitrary (arbitrary), Gen, frequency, generate, quickCheck)

------------------------------------------------
channelEffect ::
  forall m a.
  Monad m =>
  -- | Action before 'send'
  (a -> m ()) ->
  -- | Action after 'recv'
  (Maybe a -> m ()) ->
  Channel m a ->
  Channel m a
channelEffect beforeSend afterRecv Channel {send, recv} =
  Channel
    { send = \x -> do
        beforeSend x
        send x,
      recv = do
        mx <- recv
        afterRecv mx
        return mx
    }

-- | Delay a channel on the receiver end.
--
-- This is intended for testing, as a crude approximation of network delays.
-- More accurate models along these lines are of course possible.
delayChannel ::
  ( MonadSTM m,
    MonadTimer m
  ) =>
  DiffTime ->
  Channel m a ->
  Channel m a
delayChannel delay =
  channelEffect
    (\_ -> return ())
    (\_ -> threadDelay delay)

-- | Channel which logs sent and received messages.
loggingChannel ::
  ( MonadSay m,
    Show id,
    Show a
  ) =>
  id ->
  Channel m a ->
  Channel m a
loggingChannel ident Channel {send, recv} =
  Channel
    { send = loggingSend,
      recv = loggingRecv
    }
  where
    loggingSend a = do
      say (show ident ++ ":send:" ++ show a)
      send a

    loggingRecv = do
      msg <- recv
      case msg of
        Nothing -> return ()
        Just a -> say (show ident ++ ":recv:" ++ show a)
      return msg

------------------------------------------------
data Channel m a = Channel
  { send :: a -> m (),
    recv :: m (Maybe a)
  }

data DecodeStep bytes failure m a
  = DecodePartial
      ( Maybe bytes ->
        m (DecodeStep bytes failure m a)
      )
  | DecodeDone a (Maybe bytes)
  | DecodeFail failure

runDecoderWithChannel ::
  Monad m =>
  Channel m bytes ->
  Maybe bytes ->
  DecodeStep bytes failure m a ->
  m (Either failure (a, Maybe bytes))
runDecoderWithChannel Channel {recv} = go
  where
    go _ (DecodeDone x trailing) = return (Right (x, trailing))
    go _ (DecodeFail failure) = return (Left failure)
    go Nothing (DecodePartial k) = recv >>= k >>= go Nothing
    go (Just trailing) (DecodePartial k) = k (Just trailing) >>= go Nothing

mvarsAsChannel ::
  MonadSTM m =>
  TMVar m a ->
  TMVar m a ->
  Channel m a
mvarsAsChannel bufferRead bufferWrite =
  Channel {send, recv}
  where
    send x = atomically (putTMVar bufferWrite x)
    recv = atomically (Just <$> takeTMVar bufferRead)

createConnectedChannels :: MonadSTM m => m (Channel m a, Channel m a)
createConnectedChannels = do
  bufferA <- newEmptyTMVarIO
  bufferB <- newEmptyTMVarIO

  return
    ( mvarsAsChannel bufferB bufferA,
      mvarsAsChannel bufferA bufferB
    )

createConnectedBufferedChannels ::
  MonadSTM m =>
  Natural ->
  m (Channel m a, Channel m a)
createConnectedBufferedChannels sz = do
  -- Create two TBQueues to act as the channel buffers (one for each
  -- direction) and use them to make both ends of a bidirectional channel
  bufferA <- atomically $ newTBQueue sz
  bufferB <- atomically $ newTBQueue sz

  return
    ( queuesAsChannel bufferB bufferA,
      queuesAsChannel bufferA bufferB
    )
  where
    queuesAsChannel bufferRead bufferWrite =
      Channel {send, recv}
      where
        send x = atomically (writeTBQueue bufferWrite x)
        recv = atomically (Just <$> readTBQueue bufferRead)

{-# NOINLINE toLazyByteString #-}
toLazyByteString :: BS.Builder -> LBS.ByteString
toLazyByteString = BS.toLazyByteStringWith strategy LBS.empty
  where
    strategy = BS.untrimmedStrategy 800 LBS.smallChunkSize

convertCborDecoderLBS ::
  forall s m a.
  Monad m =>
  CBOR.Decoder s a ->
  (forall b. ST s b -> m b) ->
  m (DecodeStep LBS.ByteString CBOR.DeserialiseFailure m a)
convertCborDecoderLBS cborDecode liftST =
  go [] =<< liftST (CBOR.deserialiseIncremental cborDecode)
  where
    go ::
      [BS.ByteString] ->
      CBOR.IDecode s a ->
      m (DecodeStep LBS.ByteString CBOR.DeserialiseFailure m a)
    go [] (CBOR.Done trailing _ x)
      | BS.null trailing = return (DecodeDone x Nothing)
      | otherwise = return (DecodeDone x (Just trailing'))
      where
        trailing' = LBS.fromStrict trailing
    go cs (CBOR.Done trailing _ x) = return (DecodeDone x (Just trailing'))
      where
        trailing' = LBS.fromChunks (trailing : cs)
    go _ (CBOR.Fail _ _ e) = return (DecodeFail e)
    go (c : cs) (CBOR.Partial k) = go cs =<< liftST (k (Just c))
    go [] (CBOR.Partial k) = return $
      DecodePartial $ \case
        Nothing -> go [] =<< liftST (k Nothing)
        Just bs -> go cs (CBOR.Partial k)
          where
            cs = LBS.toChunks bs

convertCborEncoder :: (a -> CBOR.Encoding) -> a -> LBS.ByteString
convertCborEncoder cborEncode =
  toLazyByteString
    . CBOR.toBuilder
    . cborEncode

convertCborDecoder ::
  MonadST m =>
  (forall s. CBOR.Decoder s a) ->
  m (DecodeStep LBS.ByteString CBOR.DeserialiseFailure m a)
convertCborDecoder cborDecode =
  withLiftST (convertCborDecoderLBS cborDecode)

-------------------------------------------------------------- example

data VA
  = VA Int Bool Char
  | VB String
  deriving (Show, Eq)

instance Arbitrary VA where
  arbitrary =
    frequency
      [ (1, VA <$> arbitrary <*> arbitrary <*> arbitrary),
        (1, VB <$> arbitrary)
      ]

instance Serialise VA where
  encode = encodeVA
  decode = decodeVA

encodeVA :: VA -> Encoding
encodeVA (VA i b s) =
  encodeListLen 4 <> encodeWord 0 <> encode i <> encode b <> encode s
encodeVA (VB s) =
  encodeListLen 2 <> encodeWord 1 <> encode s

decodeVA :: Decoder s VA
decodeVA = do
  len <- decodeListLen
  tag <- decodeWord
  case (len, tag) of
    (4, 0) -> VA <$> decode <*> decode <*> decode
    (2, 1) -> VB <$> decode
    _ -> fail "failed to decode VA"

vt3 ::
  ( MonadSTM m,
    MonadST m
  ) =>
  VA ->
  m (Either DeserialiseFailure (VA, Maybe LBS.ByteString))
vt3 gva = do
  (Channel {send}, b) <- createConnectedChannels
  send (convertCborEncoder encodeVA gva)
  vt2' <- convertCborDecoder decodeVA
  runDecoderWithChannel b Nothing vt2'

-- >>> ttt
-- Right (VB "B]hJx\1067627\ACKi*]|\a\1005367\49576",Nothing)
ttt = do
  val <- generate (arbitrary :: Gen VA)
  pure $ runSimOrThrow (vt3 val)

rvt3 gva = case runSim $ vt3 gva of
  Right (Right (cva, jv)) -> cva == gva && isNothing jv
  _ -> False

q1 = quickCheck rvt3

-- SGet a resp
--- handleGet
-- SCast a msg
-- SCall a req resp

-- >>> :kind! TI IO (IO :+: Maybe)

----------------------------
class SR (b :: (Type -> Type) -> Type) (v :: (Type -> Type) -> Type) (n :: Type -> Type) where
  vsend :: TVar n (Maybe LBS.ByteString) -> v n -> Channel n LBS.ByteString -> n ()
  vrecv :: TVar n (Maybe LBS.ByteString) -> TQueue n (b n) -> Channel n LBS.ByteString -> n ()

instance
  ( MonadSTM n,
    MonadST n,
    Serialise resp,
    KnownNat (TI (SGet a resp) b),
    Inject (SGet a resp) b
  ) =>
  SR b (SGet a resp) n
  where
  vsend tvar (SGet tmvar) channel@Channel {send} = do
    let index = fromIntegral $ natVal (Proxy :: Proxy (TI (SGet a resp) b))
    send $ convertCborEncoder encodeInt index
    mval <- readTVarIO tvar
    vdec <- convertCborDecoder decode
    val <- runDecoderWithChannel channel mval vdec
    case val of
      Left e -> error (show e)
      Right (v, jl) -> do
        atomically $ writeTVar tvar jl
        atomically (putTMVar tmvar v)

  vrecv tvar tq channel@Channel {send} = do
    tmvar <- newEmptyTMVarIO
    let (sg :: SGet a resp n) = SGet tmvar
    atomically $ writeTQueue tq (inject sg)
    val' <- atomically $ takeTMVar tmvar
    send $ convertCborEncoder encode val'
    pure ()

class Grecv b n where
  grecv :: TVar n (Maybe LBS.ByteString) -> TQueue n (b n) -> Channel n LBS.ByteString -> n ()

-- instance (MonadSTM n, MonadST n, MonadFail n) => Grecv (l :+: r) n where
--   grecv tvar tq channel = do
--     mval <- readTVarIO tvar
--     vdec <- convertCborDecoder decodeInt
--     Right (val, jl) <- runDecoderWithChannel channel mval vdec
--     atomically $ writeTVar tvar jl
--     case val of
--       1 -> vrecv @(l :+: r) @l @n tvar tq channel
--       2 -> undefined
--       _ -> error "nice"

----------------------------
-- instance
--   {-# OVERLAPPABLE #-}
--   ( Serialise l,
--     Serialise r
--   ) =>
--   Serialise (l :+: r)
--   where
--   encode x = case x of
--     L l -> encodeWord 0 <> encode l
--     R r -> encodeWord 1 <> encode r

--   decode = do
--     tag <- decodeWord
--     case tag of
--       0 -> L <$> decode
--       1 -> R <$> decode
--       _ -> fail "decode :+: failed"

-- instance
--   {-# OVERLAPPABLE #-}
--   ( Serialise a,
--     Serialise b,
--     Serialise c
--   ) =>
--   Serialise (a :+: b :+: c)
--   where
--   encode x = case x of
--     L l -> encodeWord 0 <> encode l
--     R (L r) -> encodeWord 1 <> encode r
--     R (R c) -> encodeWord 2 <> encode c

--   decode = do
--     tag <- decodeWord
--     case tag of
--       0 -> L <$> decode
--       1 -> R . L <$> decode
--       2 -> R . R <$> decode
--       _ -> fail "decode :+: failed"

-- instance
--   {-# OVERLAPPABLE #-}
--   ( Serialise a,
--     Serialise b,
--     Serialise c,
--     Serialise d
--   ) =>
--   Serialise (a :+: b :+: c :+: d)
--   where
--   encode x = case x of
--     L l -> encodeWord 0 <> encode l
--     R (L r) -> encodeWord 1 <> encode r
--     R (R (L c)) -> encodeWord 2 <> encode c
--     R (R (R d)) -> encodeWord 3 <> encode d

--   decode = do
--     tag <- decodeWord
--     case tag of
--       0 -> L <$> decode
--       1 -> R . L <$> decode
--       2 -> R . R . L <$> decode
--       3 -> R . R . R <$> decode
--       _ -> fail "decode :+: failed"

-- type V = Int :+: Bool :+: VA :+: Int

-- -- >>> k
-- -- Right ("",R(R(L(VA 13 True '\1087217'))))
-- k :: IO (Either DeserialiseFailure (LBS.ByteString, V))
-- k = do
--   val <- generate (arbitrary :: Gen VA)
--   pure $
--     deserialiseFromBytes @V decode $
--       CBOR.toLazyByteString $ encode @V (R (R (L val))) -- (R (R (L 'a')))
