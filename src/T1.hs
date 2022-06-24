{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
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
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module T1 where

import Codec.CBOR.Decoding
import Codec.CBOR.Encoding
import Codec.CBOR.Read
import Codec.Serialise
import Control.Concurrent
import Control.Monad
import qualified Data.ByteString.Lazy as LBS
import Data.Data
import Data.IORef
import Data.Kind
import Data.Maybe (fromMaybe)
import GHC.Base
import GHC.TypeLits
import S
import Test.QuickCheck
import Unsafe.Coerce

type Sum :: [Type] -> Type
data Sum r where
  Sum :: Int -> t -> Sum r

instance Apply Show r => Show (Sum r) where
  show s@(Sum i _) = "Sum " ++ show i ++ " " ++ apply @Show show s

type Element t r = KnownNat (ElemIndex t r)

type t :< r = Element t r

newtype P (t :: *) (r :: [*]) = P {unP :: Int}

elemIndex :: Sum r -> Int
elemIndex (Sum n _) = n

elemNo :: forall t r. (t :< r) => P t r
elemNo = P (fromIntegral (natVal' (proxy# :: Proxy# (ElemIndex t r))))

unsafeInject :: Int -> t -> Sum r
unsafeInject = Sum
{-# INLINE unsafeInject #-}

unsafeProject :: Int -> Sum r -> Maybe t
unsafeProject n (Sum n' x)
  | n == n' = Just (unsafeCoerce x)
  | otherwise = Nothing
{-# INLINE unsafeProject #-}

inject :: forall e r. (e :< r) => e -> Sum r
inject = unsafeInject (unP (elemNo :: P e r))
{-# INLINE inject #-}

-- | Maybe project a functor out of a type-aligned sum.
project :: forall e r. (e :< r) => Sum r -> Maybe e
project = unsafeProject (unP (elemNo :: P e r))
{-# INLINE project #-}

class Apply (c :: * -> Constraint) (fs :: [*]) where
  apply :: (forall g. c g => g -> b) -> Sum fs -> b

instance (Apply Serialise r) => Serialise (Sum r) where
  encode = sumEncode
  decode = sumDecode

sumEncode :: Apply Serialise r => Sum r -> Encoding
sumEncode s@(Sum i _) = encodeListLen 2 <> encodeInt i <> apply @Serialise encode s

sumDecode :: forall r s. Apply Serialise r => Decoder s (Sum r)
sumDecode = do
  len <- decodeListLen
  i <- decodeInt
  if len == 2
    then apply @Serialise (\(_ :: k) -> Sum i <$> decode @k) (Sum i undefined :: Sum r)
    else fail "decode sum failed"

sumShrink :: Apply Arbitrary r => Sum r -> [Sum r]
sumShrink s@(Sum i _) = apply @Arbitrary (map (Sum i) . shrink) s

type family ListLength ls where
  ListLength '[] = 0
  ListLength (_ ': xs) = ListLength xs + 1

instance (Apply Arbitrary r, KnownNat (ListLength r)) => Arbitrary (Sum r) where
  arbitrary =
    oneof
      [ apply @Arbitrary (\(_ :: k) -> Sum i <$> (arbitrary :: Gen k)) (Sum i undefined :: Sum r)
        | i <- [0 .. (fromIntegral (natVal (Proxy :: Proxy (ListLength r))) - 1)]
      ]

  shrink = sumShrink

----------------------------------------- example

type K0 = Sum [Int, Bool, String, Float, Double, [Int], [Bool]]

-- >>> tq
-- Success {numTests = 1000, numDiscarded = 0, labels = fromList [(["index is 0"],136),(["index is 1"],137),(["index is 2"],144),(["index is 3"],125),(["index is 4"],146),(["index is 5"],159),(["index is 6"],153)], classes = fromList [], tables = fromList [], output = "+++ OK, passed 1000 tests:\n15.9% index is 5\n15.3% index is 6\n14.6% index is 4\n14.4% index is 2\n13.7% index is 1\n13.6% index is 0\n12.5% index is 3\n"}
tq = quickCheckResult $ withMaxSuccess 1000 prop_encode_decode

prop_encode_decode :: K0 -> Property
prop_encode_decode k@(Sum i _) =
  label ("index is " ++ show i) $
    case deserialiseFromBytes (decode @K0)
      . convertCborEncoder encode
      $ k of
      Left _ -> property False
      Right (_, dk) -> dk === k

class SR1 r a where
  sender :: IORef (Maybe LBS.ByteString) -> a -> Channel IO LBS.ByteString -> IO ()
  recver :: IORef (Maybe LBS.ByteString) -> Chan (Sum r) -> Channel IO LBS.ByteString -> IO ()

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
        print "server decode req success"
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

type F = Sum '[SCall A Int Bool, SCall A Int Int]

client :: Chan F -> IO ()
client chan = do
  mvar <- newEmptyMVar @Bool
  print "client send req"
  writeChan chan (inject $ SCall @A (10 :: Int) mvar)
  resp <- takeMVar mvar
  print $ "client response val is " ++ show resp

  mvar <- newEmptyMVar @Int
  print "client send req"
  writeChan chan (inject $ SCall @A (11 :: Int) mvar)
  resp <- takeMVar mvar
  print $ "client response val is " ++ show resp

clientLowHandler :: Chan F -> IORef (Maybe LBS.ByteString) -> Channel IO LBS.ByteString -> IO ()
clientLowHandler chan ref channel = forever $ do
  sv <- readChan chan
  clientHandler sv ref channel

-------------------------- ee

class HandleM a where
  handleM :: a -> IO ()

instance HandleM (SCall A Int Int) where
  handleM (SCall i mvar) = do
    print $ "server recv val " ++ show i
    putMVar mvar 10010
    print "server resp val 10010"

instance HandleM (SCall A Int Bool) where
  handleM (SCall i mvar) = do
    print $ "server recv val " ++ show i
    putMVar mvar True
    print "server resp val True"

server :: Chan F -> IO ()
server chan = forever $ do
  sv <- readChan chan
  apply @HandleM handleM sv

serverLowHandler :: Chan F -> IORef (Maybe LBS.ByteString) -> Channel IO LBS.ByteString -> IO ()
serverLowHandler chan ref channel = forever $ do
  serverHandler ref chan channel

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
data Cast msg

data Get resp

data Call req resp

newtype SCast t msg = SCast msg

newtype SGet t resp = SGet (MVar resp)

data SCall t req resp = SCall req (MVar resp)

---------------------------------------------------------------------------
apply2 ::
  forall c fs b.
  Apply c fs =>
  (forall g. c g => g -> g -> b) ->
  Sum fs ->
  Sum fs ->
  Maybe b
apply2 f u@(Sum n1 _) (Sum n2 r2)
  | n1 == n2 = Just (apply @c (\r1 -> f r1 (unsafeCoerce r2)) u)
  | otherwise = Nothing

instance Apply Eq r => Eq (Sum r) where
  sa == sb = fromMaybe False $ apply2 @Eq (==) sa sb

instance constraint g0 => Apply constraint '[g0] where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)

instance
  ( constraint g0,
    constraint g1
  ) =>
  Apply
    constraint
    '[ g0,
       g1
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)

instance
  ( constraint g0,
    constraint g1,
    constraint g2
  ) =>
  Apply
    constraint
    '[ g0,
       g1,
       g2
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2)

instance
  ( constraint g0,
    constraint g1,
    constraint g2,
    constraint g3
  ) =>
  Apply
    constraint
    '[ g0,
       g1,
       g2,
       g3
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2)
  apply f (Sum 3 r) = f (unsafeCoerce r :: g3)

instance
  ( constraint g0,
    constraint g1,
    constraint g2,
    constraint g3,
    constraint g4
  ) =>
  Apply
    constraint
    '[ g0,
       g1,
       g2,
       g3,
       g4
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2)
  apply f (Sum 3 r) = f (unsafeCoerce r :: g3)
  apply f (Sum 4 r) = f (unsafeCoerce r :: g4)

instance
  ( constraint g0,
    constraint g1,
    constraint g2,
    constraint g3,
    constraint g4,
    constraint g5
  ) =>
  Apply
    constraint
    '[ g0,
       g1,
       g2,
       g3,
       g4,
       g5
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2)
  apply f (Sum 3 r) = f (unsafeCoerce r :: g3)
  apply f (Sum 4 r) = f (unsafeCoerce r :: g4)
  apply f (Sum 5 r) = f (unsafeCoerce r :: g5)

instance
  ( constraint g0,
    constraint g1,
    constraint g2,
    constraint g3,
    constraint g4,
    constraint g5,
    constraint g6
  ) =>
  Apply
    constraint
    '[ g0,
       g1,
       g2,
       g3,
       g4,
       g5,
       g6
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2)
  apply f (Sum 3 r) = f (unsafeCoerce r :: g3)
  apply f (Sum 4 r) = f (unsafeCoerce r :: g4)
  apply f (Sum 5 r) = f (unsafeCoerce r :: g5)
  apply f (Sum 6 r) = f (unsafeCoerce r :: g6)

type family ElemIndex (t :: *) (ts :: [*]) :: Nat where
  ElemIndex t0 ('(:) t0 _) = 0
  ElemIndex t1 ('(:) t0 ('(:) t1 _)) = 1
  ElemIndex t2 ('(:) t0 ('(:) t1 ('(:) t2 _))) = 2
  ElemIndex t3 ('(:) t0 ('(:) t1 ('(:) t2 ('(:) t3 _)))) = 3
  ElemIndex
    t4
    ('(:) t0 ('(:) t1 ('(:) t2 ('(:) t3 ('(:) t4 _))))) =
    4
  ElemIndex
    t5
    ('(:) t0 ('(:) t1 ('(:) t2 ('(:) t3 ('(:) t4 ('(:) t5 _)))))) =
    5
  ElemIndex
    t6
    ( '(:)
        t0
        ('(:) t1 ('(:) t2 ('(:) t3 ('(:) t4 ('(:) t5 ('(:) t6 _))))))
    ) =
    6
  ElemIndex
    t7
    ( '(:)
        t0
        ( '(:)
            t1
            ('(:) t2 ('(:) t3 ('(:) t4 ('(:) t5 ('(:) t6 ('(:) t7 _))))))
        )
    ) =
    7
  ElemIndex
    t8
    ( '(:)
        t0
        ( '(:)
            t1
            ( '(:)
                t2
                ( '(:)
                    t3
                    ('(:) t4 ('(:) t5 ('(:) t6 ('(:) t7 ('(:) t8 _)))))
                )
            )
        )
    ) =
    8
  ElemIndex
    t9
    ( '(:)
        t0
        ( '(:)
            t1
            ( '(:)
                t2
                ( '(:)
                    t3
                    ( '(:)
                        t4
                        ( '(:)
                            t5
                            ( '(:)
                                t6
                                ('(:) t7 ('(:) t8 ('(:) t9 _)))
                            )
                        )
                    )
                )
            )
        )
    ) =
    9
  ElemIndex
    t
    ts =
    TypeError
      ( 'GHC.TypeLits.Text "'"
          :<>: 'GHC.TypeLits.ShowType t
          :<>: 'GHC.TypeLits.Text "' is not a member of the type-level list"
          :$$: 'GHC.TypeLits.ShowType ts
      )
