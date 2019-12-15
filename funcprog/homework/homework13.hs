

data Dir = West | North | East | South deriving (Eq, Show)

-- instance Eq Dir where
--   (==) West West   = True
--   (==) North North = True
--   (==) East East   = True
--   (==) South South = True
--   (==) _ _         = False

-- instance Show Dir where
--   show West  = "West"
--   show North = "North"
--   show East  = "East"
--   show South = "South"

type Position = (Int, Int)

type Snake = (Dir, [Position], Int)


data Instruction = Turn Dir | Move deriving (Eq, Show)

isOppositeDir :: Dir -> Dir -> Bool
isOppositeDir West East = True
isOppositeDir East West = True
isOppositeDir North South = True
isOppositeDir South North = True
isOppositeDir _ _ = False

-- test
-- isOppositeDir West East
-- isOppositeDir East West
-- isOppositeDir North South
-- isOppositeDir South North
-- not (isOppositeDir West North)
-- not (isOppositeDir North West)

nextPos :: Dir -> Position -> Position
nextPos West (x,y) = (x-1,y)
nextPos East (x,y) = (x+1,y)
nextPos South (x,y) = (x,y-1)
nextPos North (x,y) = (x,y+1)

-- test
-- nextPos West (0, 0)  == (-1, 0)
-- nextPos East (0, 0)  == (1, 0)
-- nextPos North (0, 0) == (0, 1)
-- nextPos South (0, 0) == (0, -1)
-- nextPos South (5, 9) == (5, 8)

turnHead :: Dir -> Dir -> Dir
turnHead old new | isOppositeDir old new = old
turnHead old new = new

doInstruction :: Instruction -> Snake -> Snake
doInstruction Move (direction, body, x) = (direction, (nextPos direction (head body)) : (init body), x)
doInstruction (Turn next) (direction, body, x) = (turnHead direction next, body, x)

-- test
-- doInstruction (Turn East) (North, [(5, 7), (5, 6)], 2) == (East, [(5, 7), (5, 6)], 2)
-- doInstruction (Turn East) (West, [(5, 7), (5, 6)], 2)  == (West, [(5, 7), (5, 6)], 2)
-- doInstruction Move (North, [(5, 7), (5, 6)], 2)        == (North, [(5, 8), (5, 7)], 2)
-- doInstruction Move (East, [(2, 1), (1, 1), (1, 0)], 3) == (East, [(3, 1), (2, 1), (1, 1)], 3)

