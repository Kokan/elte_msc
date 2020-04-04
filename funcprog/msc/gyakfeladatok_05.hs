{-# LANGUAGE MonadComprehensions #-}
module Notes06 where

-- Today: motivation for the Monad typeclass
-- Things shared by [] and Maybe

-- Maybe a is similuar to the type of lists of length <= 1

maybeToList :: Maybe a -> [a]
maybeToList (Just a) = [a]
maybeToList Nothing = []

maybeFromList :: [a] -> Maybe a
maybeFromList (x:_) = Just x
maybeFromList [] = Nothing

-- Both [] and Maybe are functors.
-- map :: (a -> b) -> [a] -> [b]
-- map ::

mapMaybe :: (a -> b) -> Maybe a -> Maybe b
mapMaybe f (Nothing) = Nothing
mapMaybe f (Just a) = Just (f a)

singletonList :: a -> [a]
singletonList x = [x]

singletonMaybe :: a -> Maybe a
singletonMaybe x = Just x


concatList :: [[a]] -> [a]
concatList = concat

concatMaybe :: Maybe (Maybe a) -> Maybe a
concatMaybe (Just (Just x)) = Just x
concatMaybe _ = Nothing

filterList :: (a -> Bool) -> [a] -> [a]
filterList = filter

filterMaybe :: (a -> Bool) -> Maybe a -> Maybe a
filterMaybe = undefined


-- List comprehensions
-- [ (x,y) | x <- [1..2], y <- [2..3] ]
--   == bindList (\x -> bindList (\y -> singletonList (x,y) )  [2..3]) [1..2]

bindList :: (a -> [b]) -> [a] -> [b]
bindList f [] = []
bindList f (x:xs) = (f x) <> (bindList f xs)

bindMaybe :: (a -> Maybe b) -> Maybe a -> Maybe b
bindMaybe f (Just a) = f a
bindMaybe f (Nothing) = Nothing

-- Bind is part of Monad as (>>=) :: Monad m => m a -> (a -> m b) -> m b


l4 = [ (x,y)
     | x <- [1..2]
     , y <- [2..3]
     , odd (x + y)
     ]

l5 = [ (x,y)
     | x <- Just 1
     , y <- Just 2
     , odd (x + y)
     ]


helloworld' :: IO ()
--helloworld'  [ () 


