module Bead04 where
import Prelude hiding (Semigroup(..), Monoid(..))

infixr 6 <>
class Semigroup a where
  (<>) :: a -> a -> a
  -- (x <> y) <> z == x <> (y <> z)

class Semigroup a => Monoid a where
  mempty :: a
  -- mempty <> x == x
  -- x <> mempty == x

data BinTree a = Leaf a
               | Node (BinTree a) (BinTree a)
               deriving (Eq, Show, Ord)

concatList :: Monoid a => [a] -> a
concatList [] = mempty
concatList (x:xs) = x <> concatList xs
-- ex. concatList ["abc", "def", "ghi"] = "abcdefghi"

concatTree :: Semigroup a => BinTree a -> a
concatTree (Leaf x) = x
concatTree (Node l r) = concatTree l <> concatTree r
-- ex. concatTree (Node (Leaf "abc") (Leaf "def")) == "abcdef"


-- Bead assignment 04:
--   Define Semigroup and Monoid instances for Last.
--   Last is used to find the last element in a container (list, tree, ...).

data Last a = Found a
            | NotFound
            deriving (Show, Eq)

lastcat :: Last a -> Last a -> Last a
lastcat a NotFound = a
lastcat _ b = b

instance Semigroup (Last a) where
  (<>) = lastcat

-- > concatTree (Leaf (Found 4)) == Found 4
-- > concatTree (Node (Node (Leaf (Found 1)) (Leaf (Found 2))) (Leaf (Found 3))) == Found 3
-- > concatTree (Node (Leaf (Found 'b')) (Node (Leaf (Found 'c')) (Leaf (Found 'a')))) == Found 'a'

instance Monoid (Last a) where
  mempty = NotFound

-- > concatList (map Found []) == NotFound
-- > concatList (map Found [1,1,1]) == Found 1
-- > concatList (map Found [1,2,3]) == Found 3:
