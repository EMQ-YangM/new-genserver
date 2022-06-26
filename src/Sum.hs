{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
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

module Sum where

import Data.Kind
import GHC.Base
import GHC.TypeLits
import Templates

type Sum :: [(Type -> Type) -> Type] -> (Type -> Type) -> Type
data Sum r n where
  Sum :: Int -> t n -> Sum r n

mkElemIndexTypeFamily 30

type Element t r = KnownNat (ElemIndex t r)

type t :< r = Element t r

newtype P (t :: (Type -> Type) -> Type) (r :: [(Type -> Type) -> Type]) = P {unP :: Int}

elemNo :: forall t r. (t :< r) => P t r
elemNo = P (fromIntegral (natVal' (proxy# :: Proxy# (ElemIndex t r))))

unsafeInject :: Int -> t n -> Sum r n
unsafeInject = Sum

inject :: forall e r n. (e :< r) => e n -> Sum r n
inject = unsafeInject (unP (elemNo :: P e r))

class
  Apply
    (c :: ((Type -> Type) -> Type) -> Constraint)
    (fs :: [(Type -> Type) -> Type])
  where
  apply :: (forall g. c g => g n -> b) -> Sum fs n -> b

pure (mkApplyInstance <$> [1 .. 30])

class ShowT (v :: (Type -> Type) -> Type) where
  showT :: v n -> String

instance Apply ShowT r => ShowT (Sum r) where
  showT s@(Sum i _) = "Sum " ++ show i ++ " " ++ apply @ShowT showT s
