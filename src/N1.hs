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

module N1 where

import Control.Concurrent

------------------------------------------------
data l :+: r
  = L l
  | R r

instance (Show l, Show r) => Show (l :+: r) where
  show (L l) = "L(" ++ show l ++ ")"
  show (R r) = "R(" ++ show r ++ ")"

infixr 4 :+:

class Inject a b where
  inject :: a -> b

instance Inject a a where
  inject = id

instance {-# OVERLAPPABLE #-} Inject a (a :+: b) where
  inject = L

instance {-# OVERLAPPABLE #-} (Inject a b) => Inject a (a' :+: b) where
  inject = R . (inject @a @b)

------------------------------------------------
data Get resp

data Cast msg

data Call req resp

newtype SGet a resp = SGet (MVar resp)

newtype SCast a msg = SCast msg

data SCall a req resp = SCall req (MVar resp)

instance Show (SGet a resp) where
  show (SGet _) = "SGet"

instance Show msg => Show (SCast a msg) where
  show (SCast msg) = "SCast Msg:" ++ show msg

instance Show req => Show (SCall a req resp) where
  show (SCall req _) = "SCall Req:" ++ show req

type family K a where
  K (a :: f -> b) = K1 a f

type family K1 a b where
  K1 (a :: f -> b) (Get resp) = SGet (f -> b) resp
  K1 (a :: f -> b) (Cast msg) = SCast (f -> b) msg
  K1 (a :: f -> b) (Call req resp) = SCall (f -> b) req resp

get :: forall resp a. (Get resp -> a) -> SGet (Get resp -> a) resp
get _ = SGet @(Get resp -> a) @resp undefined

cast :: forall msg a. (Cast msg -> a) -> msg -> SCast (Cast msg -> a) msg
cast _ = SCast @(Cast msg -> a) @msg

call :: forall req resp a. (Call req resp -> a) -> req -> SCall (Call req resp -> a) req resp
call _ req = SCall @(Call req resp -> a) @req @resp req undefined

------------------------------------------------ example
newtype Arg a = Arg (Call a Bool)

newtype Arg1 a = Arg1 (Call a Bool)

newtype A = A (Call Int Bool)

newtype B = B (Cast Int)

newtype C = C (Get Bool)

type Api a b =
  K 'A
    :+: K 'B
    :+: K 'C
    :+: K ('Arg @a)
    :+: K ('Arg1 @b)

-- >>> show (is 10 30)
-- "[L(SCall Req:1),R(L(SCast Msg:1)),R(R(L(SGet))),R(R(R(L(SCall Req:10)))),R(R(R(R(SCall Req:30))))]"
is :: a -> b -> [Api a b]
is a b =
  [ inject $ call A 1,
    inject $ cast B 1,
    inject $ get C,
    inject $ call Arg a,
    inject $ call Arg1 b
  ]
