{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module TS1 where

import Data.Kind
import Sum1
import Templates1
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
class HandleCall (r :: [Type]) m where
  handleCall :: HList (TMAP r m) -> Sum (TReq r) -> m (Sum (TResp r))

pure (mkHandleCallInstance <$> [1 .. 13])

-------------------------------------
type family K a where
  K (a :: f -> b) = K1 b f

type family K1 a b where
  K1 b (Call req resp) = SCall b req resp
