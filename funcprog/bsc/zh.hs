import Data.List

startEnd :: [Int] -> [Int]

startEnd [] = []
startEnd (x:[]) = [x]
startEnd xs = (head xs):(last xs):[]


tuple2List :: (a,a,a,a) -> [a]

tuple2List (a,b,c,d) = [a,b,c,d]


dlength :: [Double] -> Double
dlength [] = 0
dlength (x:xs) = 1 + (dlength xs)

avg :: [Double] -> Double

avg [] = 0
avg xs = (sum xs) / (genericLength xs)


f :: [(Int, Int)] -> Int

f [] = 0
f (x:[]) = fst x + snd x
f (x:y:xs) = sum [fst x, snd x, fst y, snd y]


foo x = (fst x) * (snd x)

dotProduct :: [Int] -> [Int] -> Int

dotProduct x y = sum (map foo (zip x y))


insertAfter :: [Int] -> Int -> Int -> [Int]

insertAfter [] f n = [n]
insertAfter (x:xs) f n | x == f = [x,n] <> xs
insertAfter (x:xs) f n = [x] ++ insertAfter (xs) f n

surrounded :: [Int] -> [Int]

surrounded [] = []
surrounded (x:[]) = []
surrounded (x:y:[]) = []
surrounded (x:y:z:xs) | x < y && y < z = [y] <> (surrounded (y:z:xs))
                      | otherwise = (surrounded (y:z:xs))

count :: [Char] -> Char -> Int
count xs x = length (filter (== x) xs)

single :: [Char] -> Char -> [Char]

single xs f |  (count xs f) >= 1 = [f]
            | otherwise = []

multiple :: [Char] -> [Char]
multiple [] = []
multiple (x:xs) = (single xs x) <> (multiple (filter (/=x) xs))

sameSign :: [Int] -> Bool

sameSign xs = ((length xs) == (length (filter (>=0) xs))) || ((length xs) == (length (filter (<=0) xs)))


data Temperature = C Double | F Double deriving (Eq, Show)

convertTemp :: Temperature -> Temperature

convertTemp (C c) = F (1.8 * c + 32)
convertTemp (F f) = C ((f - 32) / 1.8)


convert :: [Temperature] -> [Temperature]

convert [] = []
convert ((F f):xs) = (convertTemp (F f)):(convert xs)
convert ((C c):xs) = (C c):(convert xs)

alwaysC :: Temperature -> Double
alwaysC (C c) = c
alwaysC (F f) = alwaysC (convertTemp (F f))

minMaxTemp :: [Temperature] -> (Temperature, Temperature)

minMaxTemp xs = (C (minimum (map alwaysC xs)),C (maximum (map alwaysC xs)))






