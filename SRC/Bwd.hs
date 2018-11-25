{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Bwd where

data Bwd x = B0 | Bwd x :< x deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

infixl 3 :<

instance Semigroup (Bwd x) where
  (<>) = mappend

instance Monoid (Bwd x) where
  mempty = B0
  mappend yz B0 = yz
  mappend yz (xz :< x) = mappend yz xz :< x

(<?) :: Bwd x -> Int -> x
(xz :< x) <? 0 = x
(xz :< x) <? n = xz <? (n - 1)

type Lev x = (Bwd (x, Int), Int)

levPush :: Lev x -> x -> Lev x
levPush (xz, n) x = (xz :< (x, n), n + 1)

