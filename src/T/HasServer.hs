{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module T.HasServer where

import Control.Algebra
import Control.Carrier.Random.Gen
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Concurrent
import Control.Effect.Labelled (HasLabelled, Labelled, runLabelled, sendLabelled)
import Control.Monad
import Control.Monad.IO.Class
import Control.Tracer
import Data.IORef
import Data.Kind
import GHC.TypeLits
import Sum1
import System.Random (mkStdGen)
import TS1

------------------------------------------------------------------
data ClientCall (r :: [Type]) (m :: Type -> Type) (a :: Type) where
  ClientCall ::
    ( Req t req :< TReq r,
      Resp t resp :< TResp r
    ) =>
    (Call req resp -> t) ->
    req ->
    ClientCall r m resp

type SupportCall (name :: Symbol) r sig m =
  HasLabelled name (ClientCall r) sig m

call ::
  forall (name :: Symbol) r t req resp sig m.
  ( Req t req :< TReq r,
    Resp t resp :< TResp r,
    HasLabelled name (ClientCall r) sig m
  ) =>
  (Call req resp -> t) ->
  req ->
  m resp
call t req = sendLabelled @name (ClientCall t req)

------------------------------------------------------------------
data ServerCall (r :: [Type]) (m :: Type -> Type) a where
  ServerGet :: ServerCall r m (Sum (TReq r))
  ServerPut :: Sum (TResp r) -> ServerCall r m ()

type SupportHandleCall (name :: Symbol) r sig m =
  ( HasLabelled name (ServerCall r) sig m,
    HandleCall r m
  )

data ServerTracer r
  = ServerReqTracer (Sum (TReq r))
  | ServerRespTracer (Sum (TResp r))

instance
  ( Apply Show (TReq r),
    Apply Show (TResp r)
  ) =>
  Show (ServerTracer r)
  where
  show (ServerReqTracer req) = "ServerRecv " ++ show req
  show (ServerRespTracer resp) = "ServerResp " ++ show resp

serverHandleCall ::
  forall name r sig m.
  SupportHandleCall name r sig m =>
  Tracer m (ServerTracer r) ->
  HList (TMAP r m) ->
  m ()
serverHandleCall serverTracer hl = do
  va <- sendLabelled @name ServerGet
  traceWith serverTracer $ ServerReqTracer va
  ha <- handleCall @r hl va
  traceWith serverTracer $ ServerRespTracer ha
  sendLabelled @name (ServerPut ha)
