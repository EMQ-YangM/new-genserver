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

import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class
import Data.Kind
import Sum1
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
class CallHandles (r :: [Type]) m where
  callHandler :: HList (TMAP r m) -> Sum (TReq r) -> m (Sum (TResp r))

instance
  (Functor m) =>
  CallHandles
    '[ SCall t0 req0 resp0
     ]
    m
  where
  callHandler (f0 :| HNil) (Sum 0 a) = Sum 0 <$> f0 (unsafeCoerce a :: Req t0 req0)

instance
  (Functor m) =>
  CallHandles
    '[ SCall t0 req0 resp0,
       SCall t1 req1 resp1
     ]
    m
  where
  callHandler (f0 :| f1 :| HNil) (Sum 0 a) = Sum 0 <$> f0 (unsafeCoerce a :: Req t0 req0)
  callHandler (f0 :| f1 :| HNil) (Sum 1 a) = Sum 1 <$> f1 (unsafeCoerce a :: Req t1 req1)

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

type Api = [K 'A, K 'B]

handler :: MonadIO m => HList (TMAP Api m)
handler =
  (\(Req i) -> liftIO (print i) >> pure (Resp (i == 1)))
    :| (\(Req i) -> liftIO (print i) >> pure (Resp $ "respon: " ++ show i))
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
-- >>> val
-- "respon: True"
val = do
  chan <- newChan @(Sum (TReq Api), MVar (Sum (TResp Api)))
  forkIO $
    void $
      forever $ do
        (vc, mv) <- readChan chan
        res <- callHandler @Api handler vc
        putMVar mv res
  mvar <- newEmptyMVar @(Sum (TResp Api))
  forM [1 .. 10] $ \_ -> do
    call chan mvar A 1
    call chan mvar B True
    call chan mvar B False
