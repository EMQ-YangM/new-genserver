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

import Control.Concurrent
import Data.Kind
import GHC.Base
import GHC.TypeLits
import Test.QuickCheck
import Unsafe.Coerce

type Sum :: [Type] -> Type
data Sum r where
  Sum :: Int -> t -> Sum r

instance Show (Sum r) where
  show (Sum i _) = show i

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

-- >>> :kind! K
-- K :: *
-- = Sum '[Int, Bool, [Char], Float, Double, [Int]]
type K0 = Sum [Int, Bool, String, Float, Double, [Int]]

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

-- >>> t1
-- "[25,23,-5]"
t1 :: IO String
t1 = do
  k <- generate (arbitrary :: Gen K0)
  pure $ apply @F f k

-- >>> show val
-- "[0,1,5,3,1,2,4]"
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

newtype Cast msg = Cast msg

newtype Get resp = Get (MVar resp)

data Call req resp = Call req (MVar resp)

instance Show (Get resp) where
  show _ = "Get :"

instance Show (Cast msg) where
  show _ = "Cast :"

instance Show (Call req resp) where
  show _ = "Call :"

data A where
  A :: Cast Int -> A

data B where
  B :: Get Int -> B

data C where
  C :: Call Int () -> C

data D a where
  D :: Cast a -> D a

instance F A where
  f (A c) = "A" ++ show c

instance F B where
  f (B c) = "B" ++ show c

instance F C where
  f (C c) = "C" ++ show c

instance F (D a) where
  f (D c) = "D" ++ show c

type TTI a = Sum [A, B, C, D a]

-- >>> :kind! forall a. [TTI a]
-- >>> map (apply @F f) $ tti 10
-- forall a. [TTI a] :: *
-- = [Sum '[A, B, C, D a]]
-- ["BGet :","DCast :","ACast :"]
tti :: forall a. a -> [TTI a]
tti a =
  [ inject $ B $ Get (undefined :: MVar Int),
    inject $ D $ Cast a,
    inject $ A $ Cast (1 :: Int)
  ]

---------------------------------------------------------------------------
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
