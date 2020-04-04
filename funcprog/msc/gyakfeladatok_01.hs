
-- Gyakorló feladatok (ismétlés, függvények, mintaillesztés, ADT-k)
--------------------------------------------------------------------------------

-- Definiáld a "xor" műveletet Bool típuson. Használj mintaillesztést,
-- vagy Prelude-ből standard függvényt.
xor :: Bool -> Bool -> Bool
xor True _ = True
xor _ True = True
xor _ _ = False


-- Definiáld a következő függvényeket tetszőlegesen, de
-- típushelyesen és totális függvényként (nem lehet végtelen loop
-- vagy exception).
f1 :: (a, (b, (c, d))) -> (b, c)
f1 (_, (b, (c, _))) = (b, c)

f2 :: (a -> b) -> a -> b
f2 f a = (f a)

f3 :: (b -> c) -> (a -> b) -> a -> c
f3 f g a = (f (g a))

f4 :: (a -> b -> c) -> (b -> a -> c)
f4 f a b = f b a -- flip

f5 :: ((a, b) -> c) -> (a -> b -> c)
f5 f x y = f (x, y)

f6 :: (a -> (b, c)) -> (a -> b, a -> c)
f6 f = (fst . f, snd . f)

f7 :: (a -> b, a -> c) -> (a -> (b, c))
f7 (f, g) a = (f a, g a)

f8 :: (Either a b -> c) -> (a -> c, b -> c)
f8 f = (f . Left, f . Right)

f9 :: (a -> c, b -> c) -> (Either a b -> c)
--f9 (f, g) = either f g
f9 (f, g) (Left a) = f a
f9 (f, g) (Right b) = g b

-- bónusz feladat (nehéz)
f10 :: (a -> a -> b) -> ((a -> b) -> a) -> b
f10 = undefined


-- Írj egy "applyMany :: [a -> b] -> a -> [b]" függvényt, ami egy
-- listában található minden függvényt alkalmaz egy
-- értékre. Pl. "applyMany [(+10), (*10)] 10 == [20, 100]".
applyMany :: [a -> b] -> a -> [b]
applyMany [] a = []
applyMany (x:xs) a = (x a) : (applyMany xs a)


-- Definiálj egy "NonEmptyList a" típust, akár ADT-ként, akár
-- típusszinonímaként, aminek az értékei nemüres listák.
-- Define the "NonEmptyList a" type, either as ADT or 
-- as a type synonime, which entries are a non-empty lists

-- :t (:)1
-- Írj egy "fromList :: [a] -> Maybe (NonEmptyList a)" függvényt, ami
-- nemüres listát ad vissza egy standard listából, ha az input nem
-- üres.
--fromList :: [a] -> Maybe (NonEmptyList a)
--fromList [] = Nothing
--fromList (a:[]) = Just (NonEmptyList a)
--fromList (a:as) = Just (NonEmptyList a (maybe a (fromList as)))


-- Írj egy "toList :: NonEmptyList a -> [a]" függvényt, ami értelemszerűen
-- működik.


-- Definiáld a "composeAll :: [a -> a] -> a -> a" függvényt. Az eredmény legyen
-- az összes bemenő függvény kompozíciója,
-- pl. "composeAll [f, g, h] x == f (g (h x))"
composeAll :: [a -> a] -> a -> a
composeAll = undefined


-- Definiáld a "merge :: Ord a => [a] -> [a] -> [a]" függvényt, ami két nemcsökkenő
-- rendezett listát összefésül úgy, hogy az eredmény is rendezett maradjon.
merge :: Ord a => [a] -> [a] -> [a]
merge = undefined


-- (bónusz) Definiáld a "mergeSort :: Ord a => [a] -> [a]" függvényt, ami a "merge"
-- iterált felhasználásával rendez egy listát.
mergeSort :: Ord a => [a] -> [a]
mergeSort = undefined



-- (bónusz) Definiáld a "sublists :: [a] -> [[a]]" függvényt, ami a bemenő lista
-- minden lehetséges részlistáját visszaadja. Pl. "sublists [1, 2] == [[],
-- [1], [2], [1, 2]]".  A részlisták sorrendje az eredményben tetszőleges, a
-- fontos, hogy az össze részlista szerepeljen.
sublists :: [a] -> [[a]]
sublists = undefined


-- Vegyük a következő ADT-t:
data Tree a = Node a [Tree a]

-- Írj "Eq a => Eq (Tree a)" instance-t
-- Írj "mapTree :: (a -> b) -> Tree a -> Tree b" függvényt
mapTree :: (a -> b) -> Tree a -> Tree b
mapTree = undefined


-- Írj "size :: Tree a -> Int" függvényt, ami megszámolja a fában levő
-- "a"-kat. Pl. size (Node 0 [Node 1 []]) == 2

size :: Tree a -> Int
size = undefined
