
divides a b = mod b a == 0

-- test
-- divides 6 36
-- divides 2 4
-- not (divides 4 2)
-- not (divides 3 7)

triangleSides a b c = triangle a b c && triangle b c a && triangle c a b
triangle a b c = a + b > c

-- test
-- triangleSides 2 1 2
-- triangleSides 4 3 4
-- not (triangleSides 3 4 1)
-- not (triangleSides 1 4 6)
-- not (triangleSides 8 4 3)
