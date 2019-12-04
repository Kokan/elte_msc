
lastInt :: [a] -> a
lastInt [] = error "no element"
lastInt (x:[]) = x
lastInt (x:xs) = lastInt xs

-- test
-- lastInt [2,0,9]  == 9
-- lastInt [2]      == 2
-- lastInt [1..101] == 101

initIntTail :: [a] -> [a] -> [a]
initIntTail (x:[]) y = y
initIntTail (x:xs) y = initIntTail xs (y ++ [x])

initInt :: [a] -> [a]
initInt [] = error "no element"
initInt x = initIntTail x []

-- test
-- initInt [1,2,3,4] == [1,2,3]
-- initInt [1,2]     == [1]
-- initInt [1]       == []
-- initInt [1..101]  == [1..100]
-- initInt [10,8..1] == [10,8..4]
