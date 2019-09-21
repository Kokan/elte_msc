type Time = (Int, Int)

shift :: Time -> Int -> Time

shift (h,m) d = (mod (h + div (m+d) 60) 24 ,mod (m+d) 60)

-- test
-- (shift (12, 30) 15)                == (12, 45)
-- shift (22, 10) 30                 == (22, 40)
-- shift (10, 05) 60                 == (11, 05)
-- shift (12, 05) 90                 == (13, 35)
-- shift (08, 30) 90                 == (10, 00)
-- shift (23, 00) 59                 == (23, 59)
-- shift (23, 00) 60                 == (00, 00)
-- shift (22, 10) (2 * 24 * 60 + 5)  == (22, 15)
-- shift (22, 10) (3 * 24 * 60 + 65) == (23, 15)

isEarlier :: Time -> Time -> Bool

isEarlier (h1,m1) (h2,m2) = h1 < h2 || h1 == h2 && m1 < m2

-- test
-- (12, 30) `isEarlier` (13, 30)
-- (12, 30) `isEarlier` (12, 31)
-- (11, 40) `isEarlier` (12, 30)
-- not ((12, 30) `isEarlier` (12, 30))
-- not ((12, 40) `isEarlier` (12, 30))
-- not ((13, 30) `isEarlier` (12, 45))
-- not ((22, 00) `isEarlier` (08, 00))

type Event = (Time, Time, String)

createEvent :: Time -> Int -> String -> Event

createEvent t d c = (t, shift t d, c)

-- test
-- createEvent (20, 00) 90 "foci a haverokkal"          == ((20, 00), (21, 30), "foci a haverokkal")
-- createEvent (16, 15) 120 "talalkozo a Cafe Frei-ben" == ((16, 15), (18, 15), "talalkozo a Cafe Frei-ben")
-- createEvent (8, 30) 90 "Funkcprog gyakorlat"         == ((8, 30), (10, 00), "Funkcprog gyakorlat")
