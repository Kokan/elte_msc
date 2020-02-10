
isIdentifierStart :: Char -> Bool
isIdentifierStart c = elem c ['a'..'z']

-- test
-- isIdentifierStart 'a'
-- isIdentifierStart 'x'
-- not (isIdentifierStart '_')
-- not (isIdentifierStart 'A')
-- not (isIdentifierStart 'P')

isIdentifierPart :: Char -> Bool
isIdentifierPart c = isIdentifierStart c || elem c (['A'..'Z'] ++ ['0'..'9'])

-- test 
-- isIdentifierStart 'a'
-- isIdentifierStart 'x'
-- not (isIdentifierStart '_')
-- not (isIdentifierStart 'A')
-- not (isIdentifierStart 'P')

isReserved :: [Char] -> Bool
isReserved "if" = True
isReserved "then" = True
isReserved "else" = True
isReserved "module" = True
isReserved "import" = True
isReserved _ = False

-- test
-- isReserved "module"
-- isReserved "import"
-- not (isReserved "")
-- not (isReserved "even")

isValid :: [Char] -> Bool
isValid [] = False
isValid (x:[]) = isIdentifierStart x
isValid string = not (isReserved string) && isIdentifierStart (head string) && and (map isIdentifierPart (tail string))

-- test
-- isValid "even2"
-- isValid "toUpper"
-- isValid "elem"
-- isValid "f"
-- not (isValid "")
-- not (isValid "import")
-- not (isValid "True")
-- not (isValid "2elem")
-- not (isValid "mod$")
