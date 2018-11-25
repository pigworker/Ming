module Elim where

import Control.Applicative

import Bwd
import Disp
import Par
import Lisp

data Elim
  = EP String
  | EV Int
  | Elim :$ Term

type Term = Lisp Elim

pElim :: Par Elim
pElim = pWeeElim >>= pMoreElim

pWeeElim :: Par Elim
pWeeElim
  =   EV <$> pInx seekX
  <|> EP <$> iden

pMoreElim :: Elim -> Par Elim
pMoreElim e
  =   (((e :$) <$ spc <*> pTerm) >>= pMoreElim)
  <|> pure e

pTerm :: Par Term
pTerm = pLisp pElim

instance Disp Elim where
  disp e (EP x) = x
  disp e (EV i) = termDisp e <? i
  disp e (f :$ s) = disp e f ++ " " ++ disp e s

instance Show Elim where
  show = dispShow
