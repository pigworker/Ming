module Elim where

import Control.Applicative

import Bwd
import Disp
import Par
import Intv
import Lisp

data Elim
  = EP (String, Int)
  | EV Int
  | Elim :$ Term
  | EI Point
  | Term ::: Term

type Term = Lisp Elim

pElim :: Par Elim
pElim = pWeeElim >>= pMoreElim

pWeeElim :: Par Elim
pWeeElim
  =   EV <$> pInx
  <|> EP <$> pLev
  <|> EI <$ punc "{" <* spc <*> pPoint <* spc <* punc "}"
  <|> (:::) <$ punc "(" <* spc <*> pTerm <* spc
            <* punc ":" <* spc <*> pTerm <* spc
            <* punc ")"

pMoreElim :: Elim -> Par Elim
pMoreElim e
  =   (((e :$) <$ spc <*> pTerm) >>= pMoreElim)
  <|> pure e

pTerm :: Par Term
pTerm = pLisp pElim

instance Disp Elim where
  disp e (EP (x, _)) = x
  disp e (EV i) = inxNames e <? i
  disp e (f :$ s) = disp e f ++ " " ++ disp e s
  disp e (EI p) = "{" ++ disp e p ++ "}"
  disp e (tm ::: ty) = "(" ++ disp e tm ++ " : " ++ disp e ty ++ ")"

instance Show Elim where
  show = dispShow
