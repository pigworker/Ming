{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances,
             DeriveFunctor, DeriveFoldable, DeriveTraversable  #-}

module Bind where

import Control.Newtype
import Control.Applicative
import Data.Functor.Compose
import Control.Monad.Identity

import Bwd
import Disp

newtype B f x = B (f x) deriving (Functor, Foldable, Traversable)

class Traversable d => DeBruijn d where
  deBruijn :: Applicative f => (Int -> s -> f t) -> Int -> d s -> f (d t)

instance DeBruijn f => DeBruijn (B f) where
  deBruijn f i (B s) = B <$> deBruijn f (i + 1) s

data LI
  = Lev (String, Int)
  | Inx Int

instance Eq LI where
  Lev (_, i) == Lev (_, j) = i == j
  Inx i == Inx j = i == j
  _ == _ = False

instance Disp LI where
  disp _ (Lev (x, _)) = x
  disp e (Inx i) = inxNames e <? i

instance Show LI where
  show = dispShow

instance Newtype (Compose f g a) (f (g a)) where
  pack = Compose
  unpack = getCompose

instance Newtype (Identity t) t where
  pack = Identity
  unpack = runIdentity

instance Newtype n o => Newtype (a -> n) (a -> o) where
  pack = (pack.)
  unpack = (unpack.)
