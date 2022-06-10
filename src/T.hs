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

data Call req resp where
  Call :: req -> MVar resp -> Call req resp

data Cast msg where
  Cast :: msg -> Cast msg

type family GI a where
  GI (Call req resp) = req
  GI (Cast msg) = msg

type family RI a s where
  RI (Call req resp) s = MVar resp -> s
  RI (Cast msg) s = s

type family J v where
  J (v :: f n) = n

class T f n where
  t :: f n -> GI n -> RI n n

instance T f (Call req resp) where
  t _ = Call

instance T f (Cast msg) where
  t _ = Cast

data l :+: r
  = L l
  | R r

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
  Auth :: Auth (Call String Int)

data PutInt n where
  PutInt :: PutInt (Cast Int)

data PutBool n where
  PutBool :: PutBool (Cast Bool)

t0 = t Auth "hello"

t1 = t PutInt 10

t2 = t PutBool True

-- >>> :kind! I
-- I :: *
-- = Call [Char] Int :+: (Cast Int :+: Cast Bool)

type I = J 'Auth :+: J 'PutInt :+: J 'PutBool

val :: [I]
val =
  [ inject t2,
    inject t1,
    inject (t0 undefined),
    inject $ t PutInt 30
  ]
