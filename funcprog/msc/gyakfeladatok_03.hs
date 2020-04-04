
import Prelude hiding (Functor(..), Semigroup(..), Monoid(..))

infixr 6 <>
class Semigroup a where
  (<>) :: a-> a-> a
-- (x <> y) <> y == x <> (y <> z)

class Semigroup a => Monoid a where
 mempty  :: a
 -- mempty <> x == x
 -- x <> mempty == x

instance Semigroup [a] where
  (<>) = (++)

instance Monoid [a] where
  mempty = []

data BinTree a = Leaf a | Node(BinTree a) (BinTree a) deriving (Eq, Show, Ord)

mconcat :: Monoid a => [a] -> a
mconcat [] = mempty
mconcat [a] = a
mconcat (x:xs) = x <> (mconcat xs)

-- ex. mconcat ["abc", "def", "ghi"] = "abcdefghi"

concatTree :: Semigroup a => BinTree a -> a
concatTree (Leaf a) = a
concatTree (Node a b) = (concatTree a) <> (concatTree b)

-- ex. concatTree (Node (Leaf "abc") (Leaf "def")) == "abcdef"

pair_concat :: (Semigroup a, Semigroup b) => (a,b) -> (a,b) -> (a,b)
pair_concat x y = ((fst x) <> (fst y), (snd x) <> (snd y))

instance (Semigroup a, Semigroup b) => Semigroup (a,b) where
   (<>) = pair_concat

impl_concat :: (Semigroup a, Semigroup b) => (a -> b) -> (a -> b) -> (a -> b)
impl_concat f g = f <> g 

instance (Semigroup a, Semigroup b) => Semigroup (a -> b) where
   (<>) = impl_concat




