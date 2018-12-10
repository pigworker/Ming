{-# LANGUAGE FlexibleInstances,
    DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Elim where

import Control.Applicative

import Bwd
import Disp
import Par
import Bind
import Lisp
import Nope

type Term = Lisp Nope Elim

data Elim f x
  = EX x
  | Elim f x :$ f x
  | f x ::: f x
  deriving (Functor, Foldable, Traversable)

instance DeBruijn f => DeBruijn (Elim f) where
  deBruijn v i (EX x) = EX <$> v i x
  deBruijn v i (e :$ s) = (:$) <$> deBruijn v i e <*> deBruijn v i s
  deBruijn v i (tm ::: ty) = (:::) <$> deBruijn v i tm <*> deBruijn v i ty

pElim :: Par (f LI) -> Par (Elim f LI)
pElim pf = pWeeElim pf >>= pMoreElim pf

pWeeElim :: Par (f LI) -> Par (Elim f LI)
pWeeElim pf
  =   EX <$> pLI
  <|> (:::) <$ punc "[" <* spc <*> pf <* spc
            <* punc ":" <* spc <*> pf <* spc
            <* punc "]"

pMoreElim :: Par (f LI) -> Elim f LI -> Par (Elim f LI)
pMoreElim pf e
  =   (((e :$) <$ spc <*> pf) >>= pMoreElim pf)
  <|> pure e

pTerm :: Par (Term LI)
pTerm = pLisp pNope (pElim pTerm)

instance Disp (f LI) => Disp (Elim f LI) where
  disp e (EX x) = disp e x
  disp e (f :$ s) = disp e f ++ " " ++ disp e s
  disp e (tm ::: ty) = "[" ++ disp e tm ++ " : " ++ disp e ty ++ "]"

instance Disp (f LI) => Show (Elim f LI) where
  show = dispShow
