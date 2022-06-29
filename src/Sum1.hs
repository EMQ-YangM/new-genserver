{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- {-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Sum1 where

import Data.Kind
import GHC.Base
import GHC.TypeLits
import Templates1
import Unsafe.Coerce (unsafeCoerce)

type Sum :: [Type] -> Type
data Sum r where
  Sum :: {-# UNPACK #-} !Int -> t -> Sum r

mkElemIndexTypeFamily 30

type Element t r = KnownNat (ElemIndex t r)

type t :< r = Element t r

newtype P (t :: Type) (r :: [Type]) = P {unP :: Int}

elemNo :: forall t r. (t :< r) => P t r
elemNo = P (fromIntegral (natVal' (proxy# :: Proxy# (ElemIndex t r))))
{-# INLINE elemNo #-}

unsafeInject :: Int -> t -> Sum r
unsafeInject = Sum
{-# INLINE unsafeInject #-}

inject :: forall e r. (e :< r) => e -> Sum r
inject = unsafeInject (unP (elemNo :: P e r))
{-# INLINE inject #-}

unsafeProject :: Int -> Sum r -> Maybe t
unsafeProject n (Sum n' x)
  | n == n' = Just (unsafeCoerce x)
  | otherwise = Nothing
{-# INLINE unsafeProject #-}

project :: forall e r. (e :< r) => Sum r -> Maybe e
project = unsafeProject (unP (elemNo :: P e r))
{-# INLINE project #-}

class
  Apply
    (c :: Type -> Constraint)
    (fs :: [Type])
  where
  apply :: (forall g. c g => g -> b) -> Sum fs -> b

pure (mkApplyInstance <$> [1 .. 30])

instance Apply Show r => Show (Sum r) where
  show s@(Sum i v) = show i ++ apply @Show show s
