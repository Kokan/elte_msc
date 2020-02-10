
eqBool :: Bool -> Bool -> Bool
eqBool a b = a == b

class Eq' a where
  eq :: a -> a ->  Bool

instance Eq' Bool where
  eq = eqBool

eqPair :: (Eq' a, Eq' b) => (a,b) -> (a,b) -> Bool
eqPair a b = (eq (fst a) (fst b)) && (eq (snd a) (snd b))

instance (Eq' a, Eq' b) => Eq' (a, b) where
  eq = eqPair

-- Algebric data types
-- data Bool' = True
--            | False

data BinTree a = Leaf a
               | Node (BinTree a) (BinTree a)

tree :: BinTree Int
tree = Node (Node (Leaf 2) (Leaf 4)) (Leaf 5)

showBinTree :: Show a => BinTree a -> String
showBinTree (Leaf a) = show a
showBinTree (Node a b) = "(" <> (show a) <> " " <> (show b) <> ")"

instance Show a => Show (BinTree a) where
  show = showBinTree


