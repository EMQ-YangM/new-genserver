{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications, ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HasServer where

import           Control.Algebra
import           Control.Carrier.Lift
import           Control.Carrier.Reader
import           Control.Effect.Labelled
import           Control.Monad
import           Control.Monad.Class.MonadFork
import           Control.Monad.Class.MonadSTM
import           Control.Monad.Class.MonadSay
import           Control.Monad.IO.Class
import           Control.Monad.IOSim            ( runSimTrace
                                                , selectTraceEventsSay
                                                )
import           Control.Monad.IOSim.Types      ( IOSim )
import           Data.Kind
import           GHC.TypeLits
import           Method
import           Sum



type family Elem (name :: Symbol) (t :: Type) (ts :: [Type]) :: Constraint where
  Elem name t '[] =
    TypeError
      ( 'Text "server "
          :<>: 'ShowType name
          ':<>: 'Text " not add "
          :<>: 'ShowType t
          :<>: 'Text " to it method list"
      )
  Elem name t (t ': xs) = ()
  Elem name t (t1 ': xs) = Elem name t xs

type family Elem0 (name :: Symbol) (t :: Type) (ts :: [Type]) :: Constraint where
  Elem0 name t '[] =
    TypeError
      ( 'Text "server "
          :<>: 'ShowType name
          ':<>: 'Text " not support method "
          :<>: 'ShowType t
      )
  Elem0 name t (t ': xs) = ()
  Elem0 name t (t1 ': xs) = Elem0 name t xs

type family InCon (name :: Symbol) (vs :: [Type]) (ts :: [Type]) :: Constraint where
    InCon name '[] ts = ()
    InCon name (v ': vs) ts = (Elem0 name v ts, InCon name vs ts)

type family CT a where
  CT (SGet b resp) = b
  CT (SCast b msg) = b
  CT (SCall b req resp) = b

type family Map (ls :: [(Type -> Type) -> Type]) :: [Type] where
    Map '[] = '[]
    Map (x ': xs) = CT x ': Map xs

type HasServer (serverName :: Symbol) api allowMethod n sig m
    = ( HasLabelled serverName (Request n api allowMethod) sig m
      , InCon serverName allowMethod (Map api)
      , Has (Lift n) sig m
      )

type Request :: (Type -> Type) -> [(Type -> Type) -> Type] -> [Type] -> (Type -> Type) -> Type -> Type
data Request n ms allowMethod m a where
    RCall ::SCall t req resp :< ms => (Call req resp -> t) -> req -> Request n ms allowMethod m resp
    RCast ::SCast t msg :< ms => (Cast msg -> t) -> msg -> Request n ms allowMethod m ()
    RGet ::SGet t resp :< ms => (Get resp -> t) -> Request n ms allowMethod m resp

call
    :: forall (s :: Symbol) n ms sig m req resp t allowMethod
     . ( HasLabelled s (Request n ms allowMethod) sig m
       , SCall t req resp :< ms
       , Elem s t allowMethod
       )
    => (Call req resp -> t)
    -> req
    -> m resp
call t req = sendLabelled @s (RCall t req)

cast
    :: forall (s :: Symbol) n ms sig m msg t allowMethod
     . ( HasLabelled s (Request n ms allowMethod) sig m
       , SCast t msg :< ms
       , Elem s t allowMethod
       )
    => (Cast msg -> t)
    -> msg
    -> m ()
cast t msg = sendLabelled @s (RCast t msg)

get
    :: forall (s :: Symbol) n ms sig m resp t allowMethod
     . ( HasLabelled s (Request n ms allowMethod) sig m
       , SGet t resp :< ms
       , Elem s t allowMethod
       )
    => (Get resp -> t)
    -> m resp
get t = sendLabelled @s (RGet t)

type RequestC :: (Type -> Type) -> [(Type -> Type) -> Type] -> [Type] -> (Type -> Type) -> Type -> Type
newtype RequestC n ms allowMethod m a
  = RequestC { unRequestC :: ReaderC (TQueue n (Sum ms n)) m a}
  deriving (Functor , Applicative, Monad, MonadIO)

instance ( MonadSTM n, Has (Lift n) sig m) =>
  Algebra (Request n ms allowMethod :+: sig) (RequestC n ms allowMethod m) where
    alg hdl sig ctx = RequestC $ ReaderC $ \tq -> case sig of
        L (RCall (_ :: Call req resp -> t) req) -> do
            resp <- sendM @n $ do
                tmvar <- newEmptyTMVarIO
                atomically $ writeTQueue tq $ inject $ SCall @t @req @resp @n
                    req
                    tmvar
                atomically $ takeTMVar tmvar
            pure (resp <$ ctx)
        L (RCast (_ :: Cast msg -> t) msg) -> do
            sendM @n $ atomically $ writeTQueue tq $ inject $ SCast @t @msg @n
                msg
            pure ctx
        L (RGet (_ :: Get resp -> t)) -> do
            resp <- sendM @n $ do
                tmvar <- newEmptyTMVarIO
                atomically $ writeTQueue tq $ inject $ SGet @t @resp @n tmvar
                atomically $ takeTMVar tmvar
            pure (resp <$ ctx)
        R sign -> alg (runReader tq . unRequestC . hdl) sign ctx

runWithServer
    :: forall (servername :: Symbol) n ms m a allowMethod
     . TQueue n (Sum ms n)
    -> Labelled servername (RequestC n ms allowMethod) m a
    -> m a
runWithServer tq = runReader tq . unRequestC . runLabelled


----------------------------------------------------------------- exampele

data A where
    A ::Call Int String -> A

data B where
    B ::Cast String -> B

data C where
    C ::Get Int -> C

data D where
    D ::Get Int -> D

type Api = '[K 'A , K 'B , K 'C , K 'D]

client
    :: forall n sig m
     . ( HasServer "f" Api '[A , B , C , D] n sig m
       , Has (Reader (TMVar n Bool)) sig m
       , MonadSTM n
       )
    => m ()
client = do
    resp <- call @"f" A 1
    i    <- get @"f" C
    i1   <- get @"f" D
    cast @"f" B (resp ++ show i ++ show i1)
    tmvar <- ask
    sendM @n $ atomically $ putTMVar tmvar True

class HandleM a where
    handleM :: (MonadSTM n, MonadSay n) => a n -> n ()

instance HandleM (SCall A Int String) where
    handleM (SCall _ tmvar) = do
        atomically $ putTMVar tmvar "hello"

instance HandleM (SCast B String) where
    handleM (SCast msg) = say msg

instance HandleM (SGet C Int) where
    handleM (SGet mvar) = do
        atomically $ putTMVar mvar 10

instance HandleM (SGet D Int) where
    handleM (SGet mvar) = do
        atomically $ putTMVar mvar 11

instance Algebra (Lift (IOSim s)) (IOSim s) where
    alg hdl (LiftWith with) = with hdl
    {-# INLINE alg #-}

server :: (MonadSTM n, MonadSay n) => TQueue n (Sum Api n) -> n ()
server tq = forever $ do
    tv <- atomically $ readTQueue tq
    apply @HandleM handleM tv

example
    :: forall n
     . (MonadSTM n, MonadFork n, MonadSay n, Algebra (Lift n) n)
    => n ()
example = do
    tq    <- newTQueueIO
    tmvar <- newEmptyTMVarIO @_ @Bool
    forkIO . void $ server tq
    forkIO $ void $ runWithServer @"f" tq $ runReader tmvar client
    atomically $ takeTMVar tmvar
    pure ()

-- >>> runExample
-- ["hello1011"]
runExample = selectTraceEventsSay $ runSimTrace example
