{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module T where

import Control.Concurrent
import Control.Monad (forever, void)
import Data.Time

data Call req resp where
  Call :: req -> MVar resp -> Call req resp

data Cast msg where
  Cast :: msg -> Cast msg

instance Show req => Show (Call req resp) where
  show (Call req _) = "Call " ++ show req

instance Show msg => Show (Cast msg) where
  show (Cast msg) = "Cast " ++ show msg

type family GI a where
  GI (Call req resp) = req
  GI (Cast msg) = msg

type family RI a where
  RI (Call req resp) = Call req resp
  RI (Cast msg) = Cast msg

type family Res a where
  Res (_, Call req resp) = resp

type family J v where
  J (v :: f n) = (f n, n)

class T f n where
  t :: f n -> GI n -> IO (f n, RI n)

instance T f (Call req resp) where
  t f gi = do
    mvar <- newEmptyMVar
    pure (f, Call gi mvar)

instance T f (Cast msg) where
  t f gi = pure (f, Cast gi)

data l :+: r
  = L l
  | R r

instance (Show l, Show r) => Show (l :+: r) where
  show (L l) = "L (" ++ show l ++ ")"
  show (R r) = "R (" ++ show r ++ ")"

infixr 4 :+:

class Inject a b where
  inject :: a -> b

instance Inject a a where
  inject = id

instance {-# OVERLAPPABLE #-} Inject a (a :+: b) where
  inject = L

instance {-# OVERLAPPABLE #-} (Inject a b) => Inject a (a' :+: b) where
  inject = R . (inject @a @b)

class InjectCall a b where
  injectCall :: Chan b -> IO a -> IO (Res a)

instance Inject (v, Call req resp) b => InjectCall (v, Call req resp) b where
  injectCall chan a = do
    a'@(_, Call _ resp) <- a
    writeChan chan (inject a')
    takeMVar resp

class InjectCast a b where
  injectCast :: Chan b -> IO a -> IO ()

instance Inject (v, Cast msg) b => InjectCast (v, Cast msg) b where
  injectCast chan a = do
    a' <- a
    writeChan chan (inject a')

call :: (InjectCall (f n, RI n) b, T f n) => Chan b -> f n -> GI n -> IO (Res (f n, RI n))
call a b c = injectCall a (t b c)

cast :: (InjectCast (f n, RI n) b, T f n) => Chan b -> f n -> GI n -> IO ()
cast a b c = injectCast a (t b c)

-------------------------- example
data Auth n where
  Auth :: Auth (Call String Bool)

data PutInt n where
  PutInt :: PutInt (Cast Int)

data PutBool n where
  PutBool :: PutBool (Cast Bool)

data PutBool1 n where
  PutBool1 :: PutBool1 (Cast Bool)

data GetTime n where
  GetTime :: GetTime (Call () UTCTime)

-- >>> :kind! I
type I = J 'Auth :+: J 'PutInt :+: J 'PutBool :+: J 'PutBool1 :+: J 'GetTime

val :: Chan I -> IO ()
val chan = forever $ do
  val <- call chan Auth "hello"
  cast chan PutBool True
  print val
  time <- call chan GetTime ()
  print time
  threadDelay 1000009

handleI :: Chan I -> IO ()
handleI chan = forever $ do
  val <- readChan chan
  case val of
    L (_, Call s resp) -> do
      putStrLn s
      putMVar resp True
    R (L (_, Cast i)) -> print i
    R (R (L (_, Cast i))) -> print i
    R (R (R (L (_, Cast i)))) -> print i
    R (R (R (R (_, Call _ resp)))) -> do
      time <- getCurrentTime
      putMVar resp time

r :: IO ()
r = do
  chan <- newChan
  forkIO $ void $ val chan
  handleI chan
