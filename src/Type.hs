{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Type where

import Control.Algebra
import Control.Carrier.Lift
import Control.Monad.IOSim
import Data.Kind
import GHC.TypeLits
import Method

type family Elem (name :: Symbol) (t :: Type) (ts :: [Type]) :: Constraint where
  Elem name t '[] =
    TypeError
      ( 'Text "server "
          :<>: 'ShowType name
          ':<>: 'Text " not add "
          :<>: 'ShowType t
          :<>: 'Text " to it method list"
      )
  Elem name t (t ': xs) = ()
  Elem name t (t1 ': xs) = Elem name t xs

type family Elem0 (name :: Symbol) (t :: Type) (ts :: [Type]) :: Constraint where
  Elem0 name t '[] =
    TypeError
      ( 'Text "server "
          :<>: 'ShowType name
          ':<>: 'Text " not support method "
          :<>: 'ShowType t
      )
  Elem0 name t (t ': xs) = ()
  Elem0 name t (t1 ': xs) = Elem0 name t xs

type family InCon (name :: Symbol) (vs :: [Type]) (ts :: [Type]) :: Constraint where
  InCon name '[] ts = ()
  InCon name (v ': vs) ts = (Elem0 name v ts, InCon name vs ts)

type family CT a where
  CT (SGet b resp) = b
  CT (SCast b msg) = b
  CT (SCall b req resp) = b

type family AllReq (ls :: [(Type -> Type) -> Type]) :: [Type] where
  AllReq '[] = '[]
  AllReq (x ': xs) = CT x ': AllReq xs

instance Algebra (Lift (IOSim s)) (IOSim s) where
  alg hdl (LiftWith with) = with hdl
  {-# INLINE alg #-}
