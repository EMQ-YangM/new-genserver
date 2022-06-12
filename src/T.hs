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

instance Show req => Show (Call req resp) where
  show (Call req _) = "Call " ++ show req

instance Show msg => Show (Cast msg) where
  show (Cast msg) = "Cast " ++ show msg

instance Show (Get msg) where
  show (Get _) = "Get"

type family GI a where
  GI (Call req resp) = req
  GI (Cast msg) = msg

type family Res a where
  Res (_, Call req resp) = resp
  Res (_, Get resp) = resp

type family J v where
  J (v :: f n) = (f n, n)

-----------------------------------

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

data Call req resp where
  Call :: req -> MVar resp -> Call req resp

data Cast msg where
  Cast :: msg -> Cast msg

data Get resp where
  Get :: MVar resp -> Get resp

type family ResCall a where
  ResCall (Call req resp) = resp

class TCall f b req resp where
  tCall :: Chan b -> f (Call req resp) -> req -> IO resp

data SCall f req resp where
  SCall :: req -> MVar resp -> SCall f req resp

instance Inject (SCall f req resp) b => TCall f b req resp where
  tCall chan _ gi = do
    mvar <- newEmptyMVar @resp
    writeChan chan (inject (SCall @req @resp @f gi mvar))
    takeMVar mvar

type family K v where
  K (v :: f (Call req resp)) = SCall f req resp

data Auth n where
  Auth :: Auth (Call String Bool)

data Auth1 n where
  Auth1 :: Auth1 (Call String Bool)

-- data (l :: m) :++: (r :: n)
--   = NL m
--   | NR n

-- type I = 'Auth :++: 'Auth1

-- vi :: I
-- vi = NL Auth

type I = K 'Auth :+: K 'Auth1

funi :: Chan I -> IO ()
funi chan = do
  tCall chan Auth "nice"
  tCall chan Auth1 "nice1"
  pure ()

-- instance
--   Inject
--     ( f (Call req resp),
--       Call req resp
--     )
--     b =>
--   TCall f (Call req resp) b
--   where
--   tCall chan f gi = do
--     mvar <- newEmptyMVar
--     writeChan chan (inject (f, Call gi mvar))
--     takeMVar mvar

-- instance TCall f (Call req resp) where
--   tCall f gi = do
--     mvar <- newEmptyMVar
--     pure (f, Call gi mvar)

-- class TCast f n where
--   tCast :: f n -> GI n -> IO (f n, n)

-- instance TCast f (Cast msg) where
--   tCast f gi = pure (f, Cast gi)

-- class TGet f n where
--   tGet :: f n -> IO (f n, n)

-- instance TGet f (Get resp) where
--   tGet f = do
--     mvar <- newEmptyMVar
--     pure (f, Get mvar)

-----------------------------------
-- class T f n where
--   t :: f n -> GI n -> IO (f n, n)

-- instance T f (Call req resp) where
--   t f gi = do
--     mvar <- newEmptyMVar
--     pure (f, Call gi mvar)

-- instance T f (Cast msg) where
--   t f gi = pure (f, Cast gi)

-- class G f n where
--   g :: f n -> IO (f n, n)

-- instance G f (Get resp) where
--   g f = do
--     mvar <- newEmptyMVar
--     pure (f, Get mvar)

-- class InjectCall a b where
--   injectCall :: Chan b -> IO a -> IO (Res a)

-- instance
--   Inject (v, Call req resp) b =>
--   InjectCall (v, Call req resp) b
--   where
--   injectCall chan a = do
--     a'@(_, Call _ resp) <- a
--     writeChan chan (inject a')
--     takeMVar resp

-- class InjectCast a b where
--   injectCast :: Chan b -> IO a -> IO ()

-- instance
--   Inject (v, Cast msg) b =>
--   InjectCast (v, Cast msg) b
--   where
--   injectCast chan a = do
--     a' <- a
--     writeChan chan (inject a')

-- class InjectGet a b where
--   injectGet :: Chan b -> IO a -> IO (Res a)

-- instance
--   Inject (v, Get resp) b =>
--   InjectGet (v, Get resp) b
--   where
--   injectGet chan a = do
--     a'@(_, Get resp) <- a
--     writeChan chan (inject a')
--     takeMVar resp

-- get ::
--   (InjectGet (f n, n) b, G f n) =>
--   Chan b ->
--   f n ->
--   IO (Res (f n, n))
-- get a b = injectGet a (g b)

-- call ::
--   (InjectCall (f n, n) b, T f n) =>
--   Chan b ->
--   f n ->
--   GI n ->
--   IO (Res (f n, n))
-- call a b c = injectCall a (t b c)

-- cast ::
--   (InjectCast (f n, n) b, T f n) =>
--   Chan b ->
--   f n ->
--   GI n ->
--   IO ()
-- cast a b c = injectCast a (t b c)

-- -------------------------- example
-- data Auth n where
--   Auth :: Auth (Call String Bool)

-- data PutInt n where
--   PutInt :: PutInt (Cast Int)

-- data PutBool n where
--   PutBool :: PutBool (Cast Bool)

-- data PutBool1 n where
--   PutBool1 :: PutBool1 (Cast Bool)

-- data GetTime n where
--   GetTime :: GetTime (Get UTCTime)

-- -- >>> :kind! I
-- type I =
--   J 'Auth
--     :+: J 'PutInt
--     :+: J 'PutBool
--     :+: J 'PutBool1
--     :+: J 'GetTime

-- val :: Chan I -> IO ()
-- val chan = forever $ do
--   val <- call chan Auth "hello"
--   cast chan PutBool True
--   print val
--   time <- get chan GetTime
--   print time
--   threadDelay 1000009

-- handleI :: Chan I -> IO ()
-- handleI chan = forever $ do
--   val <- readChan chan
--   case val of
--     L (_, Call s resp) -> do
--       putStrLn s
--       putMVar resp True
--     R (L (_, Cast i)) -> print i
--     R (R (L (_, Cast i))) -> print i
--     R (R (R (L (_, Cast i)))) -> print i
--     R (R (R (R (_, Get resp)))) -> do
--       time <- getCurrentTime
--       putMVar resp time

-- r :: IO ()
-- r = do
--   chan <- newChan
--   forkIO $ void $ val chan
--   handleI chan
