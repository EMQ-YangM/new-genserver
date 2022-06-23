{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module T1 where

import Codec.CBOR.Decoding
import Codec.CBOR.Encoding
import Codec.CBOR.Pretty (prettyHexEnc)
import Codec.CBOR.Read
import Codec.CBOR.Write (toLazyByteString)
import Codec.Serialise
import Control.Concurrent
import qualified Data.ByteString.Lazy as LBS
import Data.Kind
import Data.Maybe (fromMaybe)
import GHC.Base
import GHC.TypeLits
import Test.QuickCheck
import Unsafe.Coerce

type Sum :: [Type] -> Type
data Sum r where
  Sum :: Int -> t -> Sum r

instance Apply Show r => Show (Sum r) where
  show s@(Sum i _) = "Sum " ++ show i ++ " " ++ apply @Show show s

type Element t r = KnownNat (ElemIndex t r)

type t :< r = Element t r

newtype P (t :: *) (r :: [*]) = P {unP :: Int}

elemIndex :: Sum r -> Int
elemIndex (Sum n _) = n

elemNo :: forall t r. (t :< r) => P t r
elemNo = P (fromIntegral (natVal' (proxy# :: Proxy# (ElemIndex t r))))

unsafeInject :: Int -> t -> Sum r
unsafeInject = Sum
{-# INLINE unsafeInject #-}

unsafeProject :: Int -> Sum r -> Maybe t
unsafeProject n (Sum n' x)
  | n == n' = Just (unsafeCoerce x)
  | otherwise = Nothing
{-# INLINE unsafeProject #-}

inject :: forall e r. (e :< r) => e -> Sum r
inject = unsafeInject (unP (elemNo :: P e r))
{-# INLINE inject #-}

-- | Maybe project a functor out of a type-aligned sum.
project :: forall e r. (e :< r) => Sum r -> Maybe e
project = unsafeProject (unP (elemNo :: P e r))
{-# INLINE project #-}

class Apply (c :: * -> Constraint) (fs :: [*]) where
  apply :: (forall g. c g => g -> b) -> Sum fs -> b

type K0 = Sum [Int, Bool, String, Float, Double, [Int]]

instance Serialise g0 => Serialise (Sum '[g0]) where
  encode (Sum 0 t) =
    encodeListLen 2
      <> encodeInt 0
      <> encode (unsafeCoerce t :: g0)
  decode = do
    len <- decodeListLen
    i <- decodeInt
    case (len, i) of
      (2, 0) -> Sum 0 <$> decode @g0
      _ -> fail "decode Sum r failed"

instance
  ( Serialise g0,
    Serialise g1
  ) =>
  Serialise
    ( Sum
        '[ g0,
           g1
         ]
    )
  where
  encode (Sum 0 t) = encodeListLen 2 <> encodeInt 0 <> encode (unsafeCoerce t :: g0)
  encode (Sum 1 t) = encodeListLen 2 <> encodeInt 1 <> encode (unsafeCoerce t :: g1)
  decode = do
    len <- decodeListLen
    i <- decodeInt
    case (len, i) of
      (2, 0) -> Sum 0 <$> decode @g0
      (2, 1) -> Sum 1 <$> decode @g1
      _ -> fail "decode Sum r failed"

instance
  ( Serialise g0,
    Serialise g1,
    Serialise g2,
    Serialise g3,
    Serialise g4,
    Serialise g5
  ) =>
  Serialise
    ( Sum
        '[ g0,
           g1,
           g2,
           g3,
           g4,
           g5
         ]
    )
  where
  encode (Sum 0 t) = encodeListLen 2 <> encodeInt 0 <> encode (unsafeCoerce t :: g0)
  encode (Sum 1 t) = encodeListLen 2 <> encodeInt 1 <> encode (unsafeCoerce t :: g1)
  encode (Sum 2 t) = encodeListLen 2 <> encodeInt 2 <> encode (unsafeCoerce t :: g2)
  encode (Sum 3 t) = encodeListLen 2 <> encodeInt 3 <> encode (unsafeCoerce t :: g3)
  encode (Sum 4 t) = encodeListLen 2 <> encodeInt 4 <> encode (unsafeCoerce t :: g4)
  encode (Sum 5 t) = encodeListLen 2 <> encodeInt 5 <> encode (unsafeCoerce t :: g5)
  decode = do
    len <- decodeListLen
    i <- decodeInt
    case (len, i) of
      (2, 0) -> Sum 0 <$> decode @g0
      (2, 1) -> Sum 1 <$> decode @g1
      (2, 2) -> Sum 2 <$> decode @g2
      (2, 3) -> Sum 3 <$> decode @g3
      (2, 4) -> Sum 4 <$> decode @g4
      (2, 5) -> Sum 5 <$> decode @g5
      _ -> fail "decode Sum r failed"

sumShrink :: Apply Arbitrary r => Sum r -> [Sum r]
sumShrink s@(Sum i _) = apply @Arbitrary (map (Sum i) . shrink) s

instance Arbitrary K0 where
  arbitrary =
    oneof
      [ inject <$> (arbitrary :: Gen Int),
        inject <$> (arbitrary :: Gen Bool),
        inject <$> (arbitrary :: Gen String),
        inject <$> (arbitrary :: Gen Float),
        inject <$> (arbitrary :: Gen Double),
        inject <$> (arbitrary :: Gen [Int])
      ]
  shrink = sumShrink

--- >>> t1
-- "3"
t1 = do
  k <- generate (arbitrary :: Gen K0)
  let a = prettyHexEnc $ encode k
      a1 = toLazyByteString $ encode k
      da = deserialiseFromBytes (decode @K0) a1
  putStrLn a
  print $ fmap (apply @F f . snd) da
  pure $ apply @F f k

tq = quickCheck prop_encode_decode

prop_encode_decode :: K0 -> Bool
prop_encode_decode k =
  let a = encode k
      a1 = toLazyByteString a
      da = deserialiseFromBytes (decode @K0) a1
   in case da of
        Left _ -> False
        Right (bs, dk) -> bs == LBS.empty && dk == k

-- >>> show val
-- "[Sum 0 1,Sum 1 True,Sum 5 [1,2,4,5],Sum 3 0.1,Sum 1 False,Sum 2 \"nice\",Sum 4 0.1]"
val :: [K0]
val =
  [ inject (1 :: Int),
    inject True,
    inject [1 :: Int, 2, 4, 5],
    inject (0.1 :: Float),
    inject False,
    inject "nice",
    inject (0.1 :: Double)
  ]

-- >>> v1
-- ["1","True","[1,2,4,5]","0.1","False","\"nice\"","0.1"]

v1 = map (apply @F f) val

class F a where
  f :: a -> String

instance F Int where
  f = show

instance F Bool where
  f = show

instance F String where
  f = show

instance F Float where
  f = show

instance F Double where
  f = show

instance F [Int] where
  f = show

---------------------------------------------------------------------------
apply2 ::
  forall c fs b.
  Apply c fs =>
  (forall g. c g => g -> g -> b) ->
  Sum fs ->
  Sum fs ->
  Maybe b
apply2 f u@(Sum n1 _) (Sum n2 r2)
  | n1 == n2 = Just (apply @c (\r1 -> f r1 (unsafeCoerce r2)) u)
  | otherwise = Nothing

instance Apply Eq r => Eq (Sum r) where
  sa == sb = fromMaybe False $ apply2 @Eq (==) sa sb

instance constraint g0 => Apply constraint '[g0] where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)

instance
  ( constraint g0,
    constraint g1
  ) =>
  Apply
    constraint
    '[ g0,
       g1
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)

instance
  ( constraint g0,
    constraint g1,
    constraint g2
  ) =>
  Apply
    constraint
    '[ g0,
       g1,
       g2
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2)

instance
  ( constraint g0,
    constraint g1,
    constraint g2,
    constraint g3
  ) =>
  Apply
    constraint
    '[ g0,
       g1,
       g2,
       g3
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2)
  apply f (Sum 3 r) = f (unsafeCoerce r :: g3)

instance
  ( constraint g0,
    constraint g1,
    constraint g2,
    constraint g3,
    constraint g4
  ) =>
  Apply
    constraint
    '[ g0,
       g1,
       g2,
       g3,
       g4
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2)
  apply f (Sum 3 r) = f (unsafeCoerce r :: g3)
  apply f (Sum 4 r) = f (unsafeCoerce r :: g4)

instance
  ( constraint g0,
    constraint g1,
    constraint g2,
    constraint g3,
    constraint g4,
    constraint g5
  ) =>
  Apply
    constraint
    '[ g0,
       g1,
       g2,
       g3,
       g4,
       g5
     ]
  where
  apply f (Sum 0 r) = f (unsafeCoerce r :: g0)
  apply f (Sum 1 r) = f (unsafeCoerce r :: g1)
  apply f (Sum 2 r) = f (unsafeCoerce r :: g2)
  apply f (Sum 3 r) = f (unsafeCoerce r :: g3)
  apply f (Sum 4 r) = f (unsafeCoerce r :: g4)
  apply f (Sum 5 r) = f (unsafeCoerce r :: g5)

type family ElemIndex (t :: *) (ts :: [*]) :: Nat where
  ElemIndex t0 ('(:) t0 _) = 0
  ElemIndex t1 ('(:) t0 ('(:) t1 _)) = 1
  ElemIndex t2 ('(:) t0 ('(:) t1 ('(:) t2 _))) = 2
  ElemIndex t3 ('(:) t0 ('(:) t1 ('(:) t2 ('(:) t3 _)))) = 3
  ElemIndex
    t4
    ('(:) t0 ('(:) t1 ('(:) t2 ('(:) t3 ('(:) t4 _))))) =
    4
  ElemIndex
    t5
    ('(:) t0 ('(:) t1 ('(:) t2 ('(:) t3 ('(:) t4 ('(:) t5 _)))))) =
    5
  ElemIndex
    t6
    ( '(:)
        t0
        ('(:) t1 ('(:) t2 ('(:) t3 ('(:) t4 ('(:) t5 ('(:) t6 _))))))
    ) =
    6
  ElemIndex
    t7
    ( '(:)
        t0
        ( '(:)
            t1
            ('(:) t2 ('(:) t3 ('(:) t4 ('(:) t5 ('(:) t6 ('(:) t7 _))))))
        )
    ) =
    7
  ElemIndex
    t8
    ( '(:)
        t0
        ( '(:)
            t1
            ( '(:)
                t2
                ( '(:)
                    t3
                    ('(:) t4 ('(:) t5 ('(:) t6 ('(:) t7 ('(:) t8 _)))))
                )
            )
        )
    ) =
    8
  ElemIndex
    t9
    ( '(:)
        t0
        ( '(:)
            t1
            ( '(:)
                t2
                ( '(:)
                    t3
                    ( '(:)
                        t4
                        ( '(:)
                            t5
                            ( '(:)
                                t6
                                ('(:) t7 ('(:) t8 ('(:) t9 _)))
                            )
                        )
                    )
                )
            )
        )
    ) =
    9
  ElemIndex
    t
    ts =
    TypeError
      ( 'GHC.TypeLits.Text "'"
          :<>: 'GHC.TypeLits.ShowType t
          :<>: 'GHC.TypeLits.Text "' is not a member of the type-level list"
          :$$: 'GHC.TypeLits.ShowType ts
      )
