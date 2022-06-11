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
import Data.Kind

data Call (l :: Type -> Type) req resp where
  Call :: req -> MVar resp -> Call l req resp

data Cast (l :: Type -> Type) msg where
  Cast :: msg -> Cast l msg

instance Show req => Show (Call l req resp) where
  show (Call req _) = "Call " ++ show req

instance Show msg => Show (Cast l msg) where
  show (Cast msg) = "Cast " ++ show msg

type family GI a where
  GI (Call l req resp) = req
  GI (Cast l msg) = msg

type family RI a where
  RI (Call l req resp) = IO (Call l req resp)
  RI (Cast l msg) = IO (Cast l msg)

type family Res a where
  Res (Call l req resp) = resp

type family J v where
  J (v :: f n) = n

class T f n where
  t :: f n -> GI n -> RI n

instance T f (Call l req resp) where
  t _ gi = Call gi <$> newEmptyMVar

instance T f (Cast l msg) where
  t _ = pure . Cast

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

instance Inject (Call l req resp) b => InjectCall (Call l req resp) b where
  injectCall chan a = do
    a'@(Call _ resp) <- a
    writeChan chan (inject a')
    takeMVar resp

class InjectCast a b where
  injectCast :: Chan b -> IO a -> IO ()

instance Inject (Cast l msg) b => InjectCast (Cast l msg) b where
  injectCast chan a = do
    a' <- a
    writeChan chan (inject a')

call :: (RI n ~ IO a, InjectCall a b, T f n) => Chan b -> f n -> GI n -> IO (Res a)
call a b c = injectCall a (t b c)

cast :: (RI n ~ IO a, InjectCast a b, T f n) => Chan b -> f n -> GI n -> IO ()
cast a b c = injectCast a (t b c)

-------------------------- example
data Auth n where
  Auth :: Auth (Call Auth String Bool)

data PutInt n where
  PutInt :: PutInt (Cast PutInt Int)

data PutBool n where
  PutBool :: PutBool (Cast PutBool Bool)

data PutBool1 n where
  PutBool1 :: PutBool1 (Cast PutBool1 Bool)

type K = [Auth, PutInt, PutBool, PutBool1]

type I = J 'Auth :+: J 'PutInt :+: J 'PutBool :+: J 'PutBool1

val :: Chan I -> IO ()
val chan = do
  val <- call chan Auth "hello"
  cast chan PutBool True
  print val
