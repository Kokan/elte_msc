

takeWord :: [Char] -> [Char]

takeWord [] = []
takeWord (' ':xs) = []
takeWord (x:xs) = x:takeWord (xs)

-- test
-- takeWord ""        == ""
-- takeWord " fa"     == ""
-- takeWord "alma fa" == "alma"
-- takeWord "almafa"  == "almafa"

dropWord :: [Char] -> [Char]

dropWord [] = []
dropWord (' ':xs) = ' ':xs
dropWord (x:xs) = dropWord xs

-- test
-- dropWord ""        == ""
-- dropWord " fa"     == " fa"
-- dropWord "alma fa" == " fa"
-- dropWord "almafa"  == ""

words' :: [Char] -> [[Char]]

words' [] = []
words' (' ':xs) = words' xs
words' xs = (takeWord xs) : (words' (dropWord xs))

-- test
-- words' ""                                                           == []
-- words' "hello"                                                      == ["hello"]
-- words' "alma fa"                                                    == ["alma","fa"]
-- words' "   Haskellben    a rekurziv fuggvenyek    mindennaposak.  " == ["Haskellben","a","rekurziv","fuggvenyek","mindennaposak."]
