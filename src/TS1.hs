{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module TS1 where

import Control.Algebra hiding (R)
import Control.Carrier.Lift
import Control.Carrier.Random.Gen
import Control.Carrier.State.Strict
import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class
import Data.Kind
import Sum1
import System.Random (mkStdGen)
import Unsafe.Coerce (unsafeCoerce)

data Call req resp

data SCall t (req :: Type) (resp :: Type)

newtype Req t req = Req req deriving (Show)

newtype Resp t resp = Resp resp deriving (Show)

-------------------------------------

type family TReq ls where
  TReq '[] = '[]
  TReq (SCall t req resp ': xs) = Req t req ': TReq xs

type family TResp ls where
  TResp '[] = '[]
  TResp (SCall t req resp ': xs) = Resp t resp ': TResp xs

type family TMAP ls m where
  TMAP '[] m = '[]
  TMAP (SCall t req resp ': xs) m = (Req t req -> m (Resp t resp)) ': TMAP xs m

data HList (ts :: [Type]) where
  HNil :: HList '[]
  (:|) :: t -> HList ts -> HList (t ': ts)

infixr 4 :|

-------------------------------------
class CallHandlers (r :: [Type]) m where
  callHandlers :: HList (TMAP r m) -> Sum (TReq r) -> m (Sum (TResp r))

instance
  (Functor m) =>
  CallHandlers
    '[ SCall t0 req0 resp0
     ]
    m
  where
  callHandlers (f0 :| HNil) (Sum 0 a) = Sum 0 <$> f0 (unsafeCoerce a :: Req t0 req0)

instance
  (Functor m) =>
  CallHandlers
    '[ SCall t0 req0 resp0,
       SCall t1 req1 resp1
     ]
    m
  where
  callHandlers (f0 :| f1 :| HNil) (Sum 0 a) = Sum 0 <$> f0 (unsafeCoerce a :: Req t0 req0)
  callHandlers (f0 :| f1 :| HNil) (Sum 1 a) = Sum 1 <$> f1 (unsafeCoerce a :: Req t1 req1)

instance
  (Functor m) =>
  CallHandlers
    '[ SCall t0 req0 resp0,
       SCall t1 req1 resp1,
       SCall t2 req2 resp2
     ]
    m
  where
  callHandlers (f0 :| f1 :| f2 :| HNil) (Sum 0 a) = Sum 0 <$> f0 (unsafeCoerce a :: Req t0 req0)
  callHandlers (f0 :| f1 :| f2 :| HNil) (Sum 1 a) = Sum 1 <$> f1 (unsafeCoerce a :: Req t1 req1)
  callHandlers (f0 :| f1 :| f2 :| HNil) (Sum 2 a) = Sum 2 <$> f2 (unsafeCoerce a :: Req t2 req2)

instance
  (Functor m) =>
  CallHandlers
    '[ SCall t0 req0 resp0,
       SCall t1 req1 resp1,
       SCall t2 req2 resp2,
       SCall t3 req3 resp3
     ]
    m
  where
  callHandlers (f0 :| f1 :| f2 :| f3 :| HNil) (Sum 0 a) = Sum 0 <$> f0 (unsafeCoerce a :: Req t0 req0)
  callHandlers (f0 :| f1 :| f2 :| f3 :| HNil) (Sum 1 a) = Sum 1 <$> f1 (unsafeCoerce a :: Req t1 req1)
  callHandlers (f0 :| f1 :| f2 :| f3 :| HNil) (Sum 2 a) = Sum 2 <$> f2 (unsafeCoerce a :: Req t2 req2)
  callHandlers (f0 :| f1 :| f2 :| f3 :| HNil) (Sum 3 a) = Sum 3 <$> f3 (unsafeCoerce a :: Req t3 req3)

-------------------------------------
type family K a where
  K (a :: f -> b) = K1 b f

type family K1 a b where
  K1 b (Call req resp) = SCall b req resp

-------------------------------------
data A where
  A :: Call Int Bool -> A

data B where
  B :: Call Bool String -> B

data C where
  C :: Call R Int -> C

data D a where
  D :: Call a Int -> D a

data R = R
  { r1 :: Int,
    r2 :: Bool,
    r3 :: String
  }
  deriving (Show)

type Api a = [K 'A, K 'B, K 'C, K ('D @a)]

handler :: (Has (State Int :+: Random) sig m, Show a) => HList (TMAP (Api a) m)
handler =
  (\(Req i) -> modify (+ i) >> pure (Resp (i == 1)))
    :| (\(Req i) -> pure (Resp $ "respon: " ++ show i))
    :| ( \(Req i) -> do
           modify (+ r1 i)
           rv <- uniformR (100, 10000)
           Resp . (+ rv) <$> get
       )
    :| (\(Req a) -> pure (Resp 1))
    :| HNil

call ::
  forall r n t req resp.
  ( Req t req :< r,
    Resp t resp :< n
  ) =>
  Chan (Sum r, MVar (Sum n)) ->
  MVar (Sum n) ->
  (Call req resp -> t) ->
  req ->
  IO resp
call chan mvar _ req = do
  writeChan chan (inject (Req @t req), mvar)
  mayberesp <- project @(Resp t resp) <$> takeMVar mvar
  case mayberesp of
    Nothing -> error "DO NOT HAPPEN"
    Just (Resp r) -> pure r

-------------------------------------
val :: IO ()
val = do
  chan <- newChan @(Sum (TReq (Api Int)), MVar (Sum (TResp (Api Int))))

  forkIO
    . void
    . runState @Int 0
    . runRandom (mkStdGen 10)
    . forever
    $ do
      (vc, mv) <- liftIO $ readChan chan
      liftIO $ print $ "recv call " ++ show vc
      res <- callHandlers @(Api Int) handler vc
      liftIO $ threadDelay 100000
      liftIO $ putMVar mv res

  mvar <- newEmptyMVar @(Sum (TResp (Api Int)))
  n <- call chan mvar C (R 1 False "nice")
  print n
  call chan mvar A 1
  n <- call chan mvar C (R 2 False "nice")
  print n
  call chan mvar B True
  n <- call chan mvar C (R 3 False "nice")
  print n
  call chan mvar B False
  call chan mvar D (1 :: Int)
  n <- call chan mvar C (R 4 False "nice")
  print n
