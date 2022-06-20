{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module T1 where

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
type K = Sum [Int, Bool, String, Float, Double, [Int]]

instance Arbitrary K where
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
  k <- generate (arbitrary :: Gen K)
  pure $ apply @F f k

-- >>> show val
-- "[0,1,5,3,1,2,4]"
val :: [K]
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
