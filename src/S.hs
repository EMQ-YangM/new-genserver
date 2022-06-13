-- copy from: https://github.com/input-output-hk/typed-protocols
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module S where

import Codec.CBOR.Decoding
import qualified Codec.CBOR.Decoding as CBOR (Decoder)
import qualified Codec.CBOR.Encoding as CBOR (Encoding)
import qualified Codec.CBOR.Read as CBOR
import qualified Codec.CBOR.Write as CBOR
import Codec.Serialise
import Codec.Serialise.Encoding
import Control.Monad (replicateM)
import Control.Monad.Class.MonadST
import Control.Monad.Class.MonadSTM
import Control.Monad.ST
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BS
import qualified Data.ByteString.Builder.Extra as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Internal as LBS (smallChunkSize)
import Test.QuickCheck (Arbitrary (arbitrary), Gen, generate)

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

data VA = VA Int Bool Char deriving (Show)

instance Arbitrary VA where
  arbitrary = VA <$> arbitrary <*> arbitrary <*> arbitrary

encodeVA :: VA -> Encoding
encodeVA (VA i b s) =
  encodeListLen 4 <> encodeWord 0 <> encode i <> encode b <> encode s

decodeVA :: Decoder s VA
decodeVA = do
  len <- decodeListLen
  tag <- decodeWord
  case (len, tag) of
    (4, 0) -> VA <$> decode <*> decode <*> decode
    _ -> fail "failed to decode VA"

-- >>> vt3
-- [Right (VA 19 False '\'',Nothing),Right (VA 28 False 'F',Nothing),Right (VA (-2) False '@',Nothing)]
vt3 :: IO [Either DeserialiseFailure (VA, Maybe LBS.ByteString)]
vt3 = replicateM 3 $ do
  (Channel {send}, b) <- createConnectedChannels
  gva <- generate (arbitrary :: Gen VA)
  send (convertCborEncoder encodeVA gva)
  vt2' <- convertCborDecoder decodeVA
  runDecoderWithChannel b Nothing vt2'
