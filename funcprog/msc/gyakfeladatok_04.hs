
-- Semigroup, Monoid, Functor
------------------------------------------------------------

import Prelude hiding (Functor(..))

class Functor f where
  fmap :: (a -> b) -> f a -> f b

-- Feladat: írj Functor instance-t az összes alábbi típushoz!

data    Foo1 a      = Foo1 Int a a a
data    Foo2 a      = Foo2 Bool a Bool
data    Foo3 a      = Foo3 a a a a a
data    Tree1 a     = Leaf1 a | Node1 (Tree1 a) (Tree1 a)
data    Tree2 a     = Node2 a [Tree2 a]
data    Pair a b    = Pair a b
data    Either' a b = Left' a | Right' b
data    Tree3 i a   = Leaf3 a | Node3 (i -> Tree3 i a)
newtype Id a        = Id a
newtype Const a b   = Const a
newtype Fun a b     = Fun (a -> b)

instance Functor Foo1 where
  fmap f (Foo1 a b c d) = Foo1 a (f b) (f c) (f d)

instance Functor Foo2 where
  fmap f (Foo2 a b c) = Foo2 a (f b) c

instance Functor Foo3 where
  fmap f (Foo3 a b c d e) = Foo3 (f a) (f b) (f c) (f d) (f e) 

instance Functor Tree1 where
  fmap f (Leaf1 a) = Leaf1 (f a)
  fmap f (Node1 a b) = (Node1 (fmap f a) (fmap f b))
--(Node2 1 [(Node2 2 [Node2 3 []])])
instance Functor Tree2 where
  fmap = undefined

instance Functor (Tree3 i) where
  fmap = undefined

instance Functor (Pair a) where
  fmap f (Pair a b) = Pair a (f b)

instance Functor (Either' a) where
  fmap f (Left' a) = Left' a
  fmap f (Right' b) = Right' (f b)

instance Functor Id where
  fmap f (Id a) = Id (f a)

instance Functor (Const a) where
  fmap f (Const a) = Const a

instance Functor (Fun a) where
  fmap = undefined
