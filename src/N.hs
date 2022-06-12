{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module N where

import Control.Algebra (alg)
import qualified Control.Algebra as A
import Control.Carrier.Reader
import Control.Concurrent
import qualified Control.Effect.Labelled as L
import Control.Monad
import Control.Monad.IO.Class
import Data.Kind
import Data.Time (UTCTime, getCurrentTime)
import GHC.TypeLits

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

--------------------------------------------
data Call req resp

data Cast msg

data Get resp

--------------------------------------------
class TCall f b req resp where
  call :: Chan b -> f (Call req resp) -> req -> IO resp

data SCall f req resp where
  SCall :: req -> MVar resp -> SCall f req resp

instance Inject (SCall f req resp) b => TCall f b req resp where
  call chan _ gi = do
    mvar <- newEmptyMVar @resp
    writeChan chan (inject (SCall @req @resp @f gi mvar))
    takeMVar mvar

--------------------------------------------
class TCast f b msg where
  cast :: Chan b -> f (Cast msg) -> msg -> IO ()

data SCast f msg where
  SCast :: msg -> SCast f msg

instance Inject (SCast f msg) b => TCast f b msg where
  cast chan _ gi = writeChan chan (inject (SCast @msg @f gi))

--------------------------------------------

class TGet f b resp where
  get :: Chan b -> f (Get resp) -> IO resp

data SGet f resp where
  SGet :: MVar resp -> SGet f resp

instance Inject (SGet f resp) b => TGet f b resp where
  get chan _ = do
    mvar <- newEmptyMVar @resp
    writeChan chan (inject (SGet @resp @f mvar))
    takeMVar mvar

--------------------------------------------
type family K v where
  K (v :: f n) = K1 f n

type family K1 f n where
  K1 f (Call req resp) = SCall f req resp
  K1 f (Cast msg) = SCast f msg
  K1 f (Get resp) = SGet f resp

-------------------------------------------- example
data Auth n where
  Auth :: Auth (Call String Bool)

data Auth1 n where
  Auth1 :: Auth1 (Call String Bool)

data PutVal n where
  PutVal :: PutVal (Cast Int)

data GetVal n where
  GetVal :: GetVal (Get UTCTime)

--------------------------------------------
data Request b (ms :: [Type -> Type]) m a where
  RCall :: TCall f b req resp => f (Call req resp) -> req -> Request b ms m resp
  RCast :: TCast f b msg => f (Cast msg) -> msg -> Request b ms m ()
  RGet :: TGet f b resp => f (Get resp) -> Request b ms m resp

type family Elem (s :: Symbol) x xs :: Constraint where
  Elem s x '[] = TypeError (Text s :<>: Text ": need add '" :<>: ShowType x :<>: Text "' to list ")
  Elem s x (x ': xs) = ()
  Elem s x (x' : xs) = Elem s x xs

type HasServer s b ms sig m = L.HasLabelled s (Request b ms) sig m

rCall ::
  forall (s :: Symbol) b ms sig m f req resp.
  ( L.HasLabelled s (Request b ms) sig m,
    TCall f b req resp,
    Elem s f ms
  ) =>
  f (Call req resp) ->
  req ->
  m resp
rCall f req = L.sendLabelled @s (RCall f req)

rCast ::
  forall (s :: Symbol) b ms sig m f msg.
  ( L.HasLabelled s (Request b ms) sig m,
    TCast f b msg,
    Elem s f ms
  ) =>
  f (Cast msg) ->
  msg ->
  m ()
rCast f req = L.sendLabelled @s (RCast f req)

rGet ::
  forall (s :: Symbol) b ms sig m f resp.
  ( L.HasLabelled s (Request b ms) sig m,
    TGet f b resp,
    Elem s f ms
  ) =>
  f (Get resp) ->
  m resp
rGet f = L.sendLabelled @s (RGet f)

newtype RequestC b ms m a = RequestC {unRequestC :: ReaderC (Chan b) m a}
  deriving (Functor, Applicative, Monad, MonadIO)

instance (MonadIO m, Algebra sig m) => Algebra (Request b ms A.:+: sig) (RequestC b ms m) where
  alg hdl sig ctx = RequestC $
    ReaderC $ \chan -> case sig of
      A.L (RCall f req) -> do
        val <- liftIO $ call chan f req
        pure (val <$ ctx)
      A.L (RCast f msg) -> do
        liftIO $ cast chan f msg
        pure ctx
      A.L (RGet f) -> do
        val <- liftIO $ get chan f
        pure (val <$ ctx)
      A.R sign -> alg (runReader chan . unRequestC . hdl) sign ctx

f1 ::
  ( HasServer "log" I '[Auth, PutVal, GetVal] sig m,
    HasServer "val" I '[Auth, PutVal, GetVal] sig m
  ) =>
  m ()
f1 = do
  v <- rCall @"val" Auth "nice"
  rCast @"log" PutVal (length $ show v)
  v <- rCall @"log" Auth "nice"
  rGet @"log" GetVal
  rCast @"log" PutVal (length $ show v)

--------------------------------------------

-- >>> :kind! I
type I = K 'Auth :+: K 'PutVal :+: K 'GetVal

funi :: Chan I -> IO ()
funi chan = forever $ do
  call chan Auth "nice"
  cast chan PutVal 10
  val <- get chan GetVal
  print val
  threadDelay 1000000

handi :: Chan I -> IO ()
handi chan = forever $ do
  val <- readChan chan
  case val of
    L (SCall req resp) -> do
      print $ "lift 1 " ++ req
      putMVar resp True
    R (L (SCast v)) -> do
      print v
    R (R (SGet resp)) -> do
      time <- getCurrentTime
      putMVar resp time

ri :: IO ()
ri = do
  chan <- newChan @I
  forkIO $ void $ funi chan
  handi chan
