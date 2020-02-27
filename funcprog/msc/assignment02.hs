

-- Pasword is 5274
{-# LANGUAGE InstanceSigs #-}
module Bead02 where

-- Bead assignment 02:
--   Define an `Ord` instance for `T`.

data T = One | Two | Three
       deriving (Eq)


t_ord :: T -> T -> Bool
t_ord One _ = True
t_ord Three Three = True
t_ord Three _ = False
t_ord Two One = False
t_ord Two Two = True
t_ord Two Three = True

instance Ord T where
  (<=) :: T -> T -> Bool
  (<=) = t_ord



