{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module TS where

import Control.Concurrent (newChan, readChan, writeChan)
import Control.Monad.IO.Class
import Data.Kind
import Sum1
import Unsafe.Coerce (unsafeCoerce)

-- Call req resp
-- Cast msg
-- data Cast msg
data Call t req resp

newtype Req t req = Req req deriving (Show)

newtype Resp t resp = Resp resp deriving (Show)

type family TMAP ls m where
  TMAP '[] m = '[]
  TMAP (Call t req resp ': xs) m = (Req t req -> m (Resp t resp)) ': TMAP xs m

type family TReq ls where
  TReq '[] = '[]
  TReq (Call t req resp ': xs) = Req t req ': TReq xs

type family TResp ls where
  TResp '[] = '[]
  TResp (Call t req resp ': xs) = Resp t resp ': TResp xs

data HList (ts :: [Type]) where
  HNil :: HList '[]
  (:|) :: t -> HList ts -> HList (t ': ts)

infixr 4 :|

---------------------------------------------------------
class CallHandles (r :: [Type]) m where
  callHandler :: HList (TMAP r m) -> Sum (TReq r) -> m (Sum (TResp r))

-- >> Call A Int Bool
instance
  (Functor m) =>
  CallHandles
    '[ Call t0 req0 resp0
     ]
    m
  where
  callHandler (f0 :| HNil) (Sum 0 a) = Sum 0 <$> f0 (unsafeCoerce a :: Req t0 req0)

instance
  (Functor m) =>
  CallHandles
    '[ Call t0 req0 resp0,
       Call t1 req1 resp1
     ]
    m
  where
  callHandler (f0 :| f1 :| HNil) (Sum 0 a) = Sum 0 <$> f0 (unsafeCoerce a :: Req t0 req0)
  callHandler (f0 :| f1 :| HNil) (Sum 1 a) = Sum 1 <$> f1 (unsafeCoerce a :: Req t1 req1)

------------------------------------
data A = A

data B = B

type Api = [Call A Int Bool, Call B Bool String]

req :: forall t req. t -> req -> Req t req
req _ = Req @t

fun1 :: MonadIO m => HList (TMAP Api m)
fun1 =
  (\(Req i) -> liftIO (print i) >> pure (Resp (i == 1)))
    :| (\(Req i) -> liftIO (print i) >> pure (Resp $ "nice" ++ show i))
    :| HNil

-- >>> val
-- Just (Resp "niceTrue")
val = do
  chan <- newChan @(Sum (TReq Api))
  writeChan chan (inject $ Req @B @Bool True)
  vc <- readChan chan
  (project @(Resp B String)) <$> callHandler @Api @IO fun1 vc

---------------------------------------

-- type FF =
--   FCall
--     [Req A Int, Req B Bool]
--     [Resp A Bool, Resp B String]

--- FCall [Req A Int, Req B Bool]
-- priority queue
