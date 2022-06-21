{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module T2 where

import Control.Concurrent
import T1

newtype Cast msg = Cast msg

newtype Get resp = Get (MVar resp)

data Call req resp = Call req (MVar resp)

instance Show (Get resp) where
  show _ = "Get :"

instance Show msg => Show (Cast msg) where
  show (Cast msg) = "Cast :" ++ show msg

instance Show req => Show (Call req resp) where
  show (Call req _) = "Call :" ++ show req

newtype A = A (Cast Int)

newtype B = B (Get Int)

newtype C = C (Call Int ())

newtype D a = D (Cast a)

instance F A where
  f (A c) = "A" ++ show c

instance F B where
  f (B c) = "B" ++ show c

instance F C where
  f (C c) = "C" ++ show c

instance Show a => F (D a) where
  f (D c) = "D" ++ show c

type TTI a = Sum [A, B, C, D a]

-- >>> :kind! forall a. [TTI a]
-- >>> tti1
-- forall a. [TTI a] :: *
-- = [Sum '[A, B, C, D a]]
-- ["BGet :","DCast :True","ACast :0","CCall :0"]

-- tti1 :: [String]
-- tti1 = map (apply @F f) $ tti True

-- tti :: forall a. a -> [TTI a]
-- tti a =
--   [ inject $ B $ Get (undefined :: MVar Int),
--     inject $ D $ Cast a,
--     inject $ A $ Cast 0,
--     inject $ C $ Call 0 undefined
--   ]
