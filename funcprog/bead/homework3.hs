nand :: Bool -> Bool -> Bool
nand True True = False
nand _ _ = True

-- test
-- not (nand True True)
-- nand True False
-- nand False True

-- well I hope you do not consider pattern matching as equation checking as sure haskell does :)
onAxis :: (Eq a, Num a) => (a, a) -> Bool
onAxis (0, _) = True
onAxis (_, 0) = True
onAxis (_, _) = False

-- test
-- onAxis (0, 0)
-- onAxis (0, 100)
-- onAxis (50, 0)
-- onAxis (-12, 0)
-- not (onAxis (4, 5)

punctuation :: Char -> Bool
punctuation '?' = True
punctuation '!' = True
punctuation '.' = True
punctuation _ = False

-- test
-- punctuation '?'
-- punctuation '!'
-- punctuation '.'
-- not (punctuation 'X')
-- not (punctuation ' ')

