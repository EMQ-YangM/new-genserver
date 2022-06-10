{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
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
  RI (Call l req resp) = MVar resp -> Call l req resp
  RI (Cast l msg) = Cast l msg

type family J v where
  J (v :: f n) = n

class T f n where
  t :: f n -> GI n -> RI n

instance T f (Call l req resp) where
  t _ = Call

instance T f (Cast l msg) where
  t _ = Cast

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

data Auth n where
  Auth :: Auth (Call Auth String Bool)

data PutInt n where
  PutInt :: PutInt (Cast PutInt Int)

data PutBool n where
  PutBool :: PutBool (Cast PutBool Bool)

data PutBool1 n where
  PutBool1 :: PutBool1 (Cast PutBool1 Bool)

t0 = t Auth "hello"

t1 = t PutInt 10

t2 = t PutBool True

-- >>> :kind! I
-- I :: *
-- = Call Auth [Char] Bool
--   :+: (Cast PutInt Int
--        :+: (Cast PutBool Bool :+: Cast PutBool1 Bool))

type I = J 'Auth :+: J 'PutInt :+: J 'PutBool :+: J 'PutBool1

-- >>> show val
-- "[R (R (L (Cast False))),R (R (R (Cast False)))]"
val :: [I]
val =
  [ inject $ t PutBool False,
    inject $ t PutBool1 False
  ]
