-- Password = 20869
{-# LANGUAGE InstanceSigs #-}
module Bead01 where

-- Bead assignment 01:
--   Define an `Eq` instance for `Sum a b`.

data Sum a b = Inj1 a | Inj2 b
-- Sum in Prelude: data Either a b = Left a | Right b
-- (But an Eq instance is already defined for Either)

_eqSum :: (Eq a, Eq b) => Sum a b -> Sum a b -> Bool
_eqSum (Inj1 a) (Inj1 b) = a == b
_eqSum (Inj2 a) (Inj2 b) = a == b
_eqSum _ _ = False


instance (Eq a, Eq b) => Eq (Sum a b) where
  (==) :: (Eq a, Eq b) => Sum a b -> Sum a b -> Bool
  (==) = _eqSum

-----------
-- Tests --
-----------

s1, s2, s3, s4 :: Sum Int Int
s1 = Inj1 0
s2 = Inj1 5
s3 = Inj2 0
s4 = Inj2 5

s5, s6, s7, s8 :: Sum [Int] [Bool]
s5 = Inj1 []
s6 = Inj1 [2]
s7 = Inj2 [False]
s8 = Inj2 [False,True]

tests :: [Bool]
tests = [ s1 == s1
        , s2 == s2
        , s3 == s3
        , s4 == s4
        , s5 == s5
        , s6 == s6
        , s7 == s7
        , s8 == s8
        , not $ s1 == s2
        , not $ s2 == s3
        , not $ s3 == s4
        , not $ s4 == s1
        , not $ s5 == s6
        , not $ s6 == s7
        , not $ s7 == s8
        , not $ s8 == s5
        ]

allTests :: Bool
allTests = all (== True) tests

-- `allTests` should be True
