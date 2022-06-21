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
import qualified T1 as T1

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

newtype SGet resp = SGet (MVar resp)

newtype SCast msg = SCast msg

data SCall req resp = SCall req (MVar resp)

instance Show (SGet resp) where
  show (SGet _) = "SGet"

instance Show msg => Show (SCast msg) where
  show (SCast msg) = "SCast Msg:" ++ show msg

instance Show req => Show (SCall req resp) where
  show (SCall req _) = "SCall Req:" ++ show req

type family K a where
  K (_ :: f -> b) = K1 f

type family K1 f where
  K1 (Get resp) = SGet resp
  K1 (Cast msg) = SCast msg
  K1 (Call req resp) = SCall req resp

get :: forall resp a. (Get resp -> a) -> SGet resp
get _ = SGet @resp undefined

cast :: forall msg a. (Cast msg -> a) -> msg -> SCast msg
cast _ = SCast @msg

call :: forall a req resp. (Call req resp -> a) -> req -> SCall req resp
call _ req = SCall @req @resp req undefined

------------------------------------------------ example
newtype Arg a = Arg (Call a Bool)

newtype Arg1 a = Arg1 (Call a Bool)

newtype A = A (Call Int Bool)

newtype B = B (Cast Int)

newtype C = C (Get Bool)

data SigV a b where
  SigV1 :: SCall a b -> SigV a b

-- >>> :kind! Api1 Int String
-- Api1 Int String :: *
-- = Sum
--     '[SCall Int Bool, SCast Int, SGet Bool, SCall Int Bool,
--       SCall [Char] Bool]
type Api1 a b =
  T1.Sum
    '[ K 'A,
       K 'B,
       K 'C,
       K ('Arg @a),
       K ('Arg1 @b)
     ]

-- >>> show (t1t 10 30)
-- "[0,1,2]"
-- t1t :: forall a b. a -> b -> [Api1 a b]
-- t1t a b =
--   [ T1.inject $ call A 1,
--     T1.inject $ cast B 1,
--     T1.inject $ get C
--     -- T1.inject $ call @(Arg a) Arg a
--   ]

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
    inject $ get C
    -- inject $ call Arg a
    -- inject $ call Arg1 b
  ]
