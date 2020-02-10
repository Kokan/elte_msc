type LookUpTable = [(Char, Char)]

rotate :: Int -> [a] -> [a]
rotate = drop <> take

generate_caesar_table :: Int -> [Char] -> LookUpTable
generate_caesar_table shift symbols = zip symbols (rotate shift symbols)

table :: LookUpTable
table = (' ', ' ') : generate_caesar_table 3 ['a'..'z']

-- test
-- (' ', ' ') `elem` table
-- ('a', 'd') `elem` table
-- ('b', 'e') `elem` table
-- ('x', 'a') `elem` table
-- ('y', 'b') `elem` table

shift :: LookUpTable -> Char -> Char
shift t e = maybe '#' id (lookup e t)


-- test
-- shift table ' ' == ' '
-- shift table 'a' == 'd'
-- shift table 'b' == 'e'
-- shift table 'x' == 'a'
-- shift table 'y' == 'b'
-- shift table '!' == '#'
-- shift [('b', 'g'), ('c', 'h'), ('a', 'f')] 'a' == 'f'
-- shift [('b', 'g'), ('c', 'h'), ('a', 'f')] 'b' == 'g'
-- shift [('b', 'g'), ('c', 'h'), ('a', 'f')] 'b' == 'g'
-- shift [('b', 'g'), ('c', 'h'), ('a', 'f')] 'x' == '#'

encrypt :: LookUpTable -> [Char] -> [Char]
encrypt t w = map (shift  t) w

-- test
-- encrypt table "abcd"           == "defg"
-- encrypt table "hello"          == "khoor"
-- encrypt table "haskell is fun" == "kdvnhoo lv ixq" 
-- encrypt table "wxyz"           == "zabc"
-- encrypt table ""               == ""
-- encrypt [('p', 'p'), ('g', 'n'), ('u', 'a')] "pug" == "pan"
