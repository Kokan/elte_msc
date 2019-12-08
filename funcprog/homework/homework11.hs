import Data.List

xor = (/=) :: Bool -> Bool -> Bool

fields = (,) <$> [0..7] <*> [0..7]

rook :: (Int, Int) -> [(Int, Int)]

rook (x,y) = filter ((/=) <$> ((==x) . fst) <*> ((==y) . snd)) fields


-- test
-- sort (rook (0,0)) == sort [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)]
-- sort (rook (7,7)) == sort [(0,7),(1,7),(2,7),(3,7),(4,7),(5,7),(6,7),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6)]

knight :: (Int, Int) -> [(Int, Int)]

knight (x,y) = filter ((==abs (x+y-3)) <$> ((+) <$> fst <*> snd)) fields

-- test
-- sort (knight (0,0)) == sort [(2,1),(1,2)]
-- sort (knight (4,6)) == sort [(6,7),(6,5),(5,4),(3,4),(2,7),(2,5)]
-- sort (knight (3,2)) == sort [(5,3),(5,1),(4,4),(4,0),(2,4),(2,0),(1,3),(1,1)]


