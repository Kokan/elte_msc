
module Bead03 where

-- Bead assignment 03:
--   Define functions f1 and f2 with the following type signatures.

f1 :: a -> (a -> b) -> (a -> b -> c) -> c
f1 a f g = g a (f a)

f2 :: Either (a -> b) (a -> c)  ->  a  ->  Either b c
f2 (Left f) a = (Left (f a))
f2 (Right f) a = (Right (f a))



