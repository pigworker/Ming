{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
    FlexibleInstances #-}

module Meta where

import Control.Applicative

import Bwd
import Lisp
import Elim
import Par
import Bind
import Disp

type Meta = Lisp MVar Elim

data MVar f x
  = String :! Bwd (Elim f x)
  deriving (Functor, Foldable, Traversable)

pMVar :: Par (f LI) -> Par (MVar f LI)
pMVar pf = (:!) <$> iden <* spc <*>
           pBwd (id <$ punc "/" <* spc <*> pElim pf)

pMeta :: Par (Meta LI)
pMeta = pLisp (pMVar pMeta) (pElim pMeta)

instance DeBruijn f => DeBruijn (MVar f) where
  deBruijn f i (m :! tz) = (m :!) <$> traverse (deBruijn f i) tz

instance Disp (f LI) => Disp (MVar f LI) where
  disp e (m :! tz) = m ++ foldMap (('/' :) <$> disp e) tz

instance Disp (f LI) => Show (MVar f LI) where
  show = dispShow
