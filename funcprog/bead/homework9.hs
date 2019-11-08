

runs :: Int -> [a] -> [[a]]
runs _ [] = []
runs n a = (take n a):runs n (drop n a)

-- test
-- runs 3 [1..10]             == [[1, 2, 3], [4, 5, 6], [7, 8, 9], [10]]
-- runs 2 "Haskell"           == ["Ha", "sk", "el", "l"]
-- runs 5 [True, True, False] == [[True, True, False]]
-- runs 4 []                  == []

join :: [a] -> [[a]] -> [a]
join _ [] = []
join e (x:[]) = x
join e (x:xs) = x <> e <> (join e xs)
