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

module TSE1 where

import Control.Algebra hiding (R)
import Control.Carrier.Random.Gen
import Control.Carrier.State.Strict
import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class
import Sum1
import System.Random (mkStdGen)
import TS1

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
      res <- handleCall @(Api Int) handler vc
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
