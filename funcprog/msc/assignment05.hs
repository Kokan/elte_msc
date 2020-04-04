module Bead05 where

-- Bead assignment 04:
--   Define Functor instances for A and B

data A a = A a Int a
         deriving (Show, Eq)

data B a = B1 [a]
         | B2 (Maybe a)
         deriving (Show, Eq)


instance Functor A where
   fmap f (A a b c) = A (f a) b (f c) 

instance Functor B where
   fmap f (B2 Nothing) = B2 Nothing
   fmap f (B2 (Just a)) = B2 (Just (f a))
   fmap f (B1 a) = B1 (fmap f a)
