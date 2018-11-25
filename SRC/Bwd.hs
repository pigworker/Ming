{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Bwd where

data Bwd x = B0 | Bwd x :< x deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

(<?) :: Bwd x -> Int -> x
(xz :< x) <? 0 = x
(xz :< x) <? n = xz <? (n - 1)

type Lev x = (Bwd (x, Int), Int)

levPush :: Lev x -> x -> Lev x
levPush (xz, n) x = (xz :< (x, n), n + 1)
