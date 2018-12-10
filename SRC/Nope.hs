{-# LANGUAGE KindSignatures #-}

module Nope where

import Control.Applicative

import Par
import Bind
import Lisp
import Disp

data Nope (f :: * -> *) (x :: *)

nope :: Nope f x -> a
nope n = n `seq` nope n

pNope :: Par (Nope f x)
pNope = empty

instance Functor (Nope f) where
  fmap _ = nope

instance Foldable (Nope f) where
  foldMap _ = nope

instance Traversable (Nope f) where
  traverse _ = nope

instance DeBruijn (Nope f) where
  deBruijn _ _ = nope

instance Show (Nope f x) where
  show = nope

instance Disp (Nope f x) where
  disp _ = nope
