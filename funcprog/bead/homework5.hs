import Data.List

compress :: (Eq a) => [a] -> [(Int,a)]
compress xs = map (\x -> (length(x), (head x))) (group xs)

-- test
-- compress "aaaabccaadeeee" == [(4,'a'), (1,'b'), (2,'c'), (2,'a'), (1,'d'), (4,'e')]
-- compress "oh hello!!"     == [(1,'o'),(1,'h'),(1,' '),(1,'h'),(1,'e'),(2,'l'),(1,'o'),(2,'!')]
-- compress ""               == []


decompressA :: [(Int,a)] -> [a] -> [a]
decompressA [] r = r
decompressA (x:xs) r =  decompressA xs (r ++ replicate (fst x) (snd x))

decompress :: [(Int,a)] -> [a]
decompress xs = decompressA xs []
--decompress [] = []
--decompress xs = replicate (fst (head xs)) (snd (head xs)) ++ decompress (tail xs)


-- test
-- decompress [(4,'a'), (1,'b'), (2,'c'), (2,'a'), (1,'d'), (4,'e')]            == "aaaabccaadeeee"
-- decompress [(1,'o'),(1,'h'),(1,' '),(1,'h'),(1,'e'),(2,'l'),(1,'o'),(2,'!')] == "oh hello!!"
-- decompress [] == ""
