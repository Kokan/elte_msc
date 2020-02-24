
module Notes02 where

-- xs = [x1, x2, x3, ...] x1 <= x2, x2 <= x3, ...
-- ys = [y1, y2, y3, ...] y1 <= y2, y2 <= y3, ...
-- 
-- merge xs zs is the sorted list with the elements of xs zy
-- merge [1,4, 9] [2, 3, 8] = [1,2,3,4,8,9]

-- merge :: Ord a => [a] -> [a] -> [a]
-- merge [] [] = []
-- merge [] ys = ys
-- merge xs [] = xs
-- merge (x:xs) (y:ys) = [min x y] <> (merge xs ((max x y):ys))

-- Bonus: use merge to define 
--         mergeSort :: Ord a => [a] -> [a]
-- Bonus2:  use
-- fib = 1 : 1 : zipWith (+) fib (tail fib)
-- fib = [1,1,2,4,5,8,13,...]
-- use merge to define an infinite list that contains
--  all powers of the elements of fib

-- group' :: Eq a => [a] -> [[a]]
-- group' [] = []
-- group' (x:xs) = [x] : (group' xs)

-- group' [x,y,y,x,z,z] = [[x],[y,y],[x],[z,z]]

data Tree a = Leaf a | Node (Tree a) (Tree a) deriving (Eq, Ord, Show)

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f (Leaf a) = (Leaf (f a))
mapTree f (Node n1 n2) = (Node (mapTree f n1) (mapTree f n2))

-- sum all elements in a tree
sumTree :: Num a => Tree a -> a
sumTree (Leaf a) = a
sumTree (Node n1 n2) = (sumTree n1) +  (sumTree n2)

-- list all elements in a tree
flattenTree :: Tree a -> [a]
flattenTree (Leaf a) = [a]
flattenTree (Node n1 n2) = (flattenTree n1) <> (flattenTree n2)

