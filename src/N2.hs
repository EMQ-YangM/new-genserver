{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
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

module N2 where

import Control.Monad.Class.MonadSTM
import Data.Kind
import GHC.TypeLits

------------------------------------------------
data (l :+: r) (n :: Type -> Type)
  = L (l n)
  | R (r n)

instance (Show (l n), Show (r n)) => Show ((l :+: r) n) where
  show (L l) = "L(" ++ show l ++ ")"
  show (R r) = "R(" ++ show r ++ ")"

infixr 4 :+:

class Inject (a :: (Type -> Type) -> Type) b where
  inject :: a n -> b n

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

newtype SGet a resp n = SGet (TMVar n resp)

newtype SCast a msg n = SCast msg

data SCall a req resp n = SCall req (TMVar n resp)

instance Show (SGet a resp n) where
  show (SGet _) = "SGet"

instance Show msg => Show (SCast a msg n) where
  show (SCast msg) = "SCast Msg:" ++ show msg

instance Show req => Show (SCall a req resp n) where
  show (SCall req _) = "SCall Req:" ++ show req

type family K a where
  K (a :: f -> b) = K1 b f

type family K1 a b where
  K1 b (Get resp) = SGet b resp
  K1 b (Cast msg) = SCast b msg
  K1 b (Call req resp) = SCall b req resp

get :: forall n resp a. (Get resp -> a) -> SGet a resp n
get _ = SGet undefined

cast :: forall n msg a. (Cast msg -> a) -> msg -> SCast a msg n
cast _ = SCast

call :: forall n req resp a. (Call req resp -> a) -> req -> SCall a req resp n
call _ req = SCall req undefined

type family TI (a :: (Type -> Type) -> Type) b where
  TI a (a :+: b) = 1
  TI a (a' :+: b) = 1 + TI a b

-- ------------------------------------------------ example

newtype Arg a = Arg (Call a Bool)

newtype Arg1 a = Arg1 (Call a Bool)

newtype A = A (Call Int Bool)

newtype B = B (Cast Int)

newtype C = C (Get Bool)

-- >>> :kind! TI  (SGet C Int ) (Api Int Bool)
-- TI  (SCast B Int ) (Api Int Bool) :: Natural
-- = 2

type Api a b =
  K 'A
    :+: K 'B
    :+: K 'C
    :+: K ('Arg @a)
    :+: K ('Arg1 @b)

-- >>> show (is 10 30)
-- "[L(SCall Req:1),R(L(SCast Msg:1)),R(R(L(SGet))),R(R(R(L(SCall Req:10)))),R(R(R(R(SCall Req:30))))]"
is :: a -> b -> [Api a b n]
is a b =
  [ inject $ call A 1,
    inject $ cast B 1,
    inject $ get C,
    inject $ call Arg a,
    inject $ call Arg1 b
  ]
