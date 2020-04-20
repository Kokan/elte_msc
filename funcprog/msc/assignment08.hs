module Bead08 where

-- Bead assignment 08:
--   Use do-notation to define the functions `ifM` and `filterM`.

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM c a b = do
    c' <- c
    if c' then a else b

filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
filterM f [] = return []
filterM f (x:xs) = do
     fx  <- f x
     fxs <- filterM f xs
     if fx then return (x:zs)  else return zs
     
-- Remembering the definition of filter may be useful:
--  filter :: (a -> Bool) -> [a] -> [a]
--  filter f [] = []
--  filter f (x:xs) = if f x
--                    then x : filter f xs
--                    else filter f xs:
