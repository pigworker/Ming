module Lisp where

import Control.Applicative

import Bwd
import Intv
import Disp
import Par

data Lisp t
  = A String
  | Lisp t :& Lisp t
  | String :. Lisp t
  | String :! Lisp t
  | I Point
  | E t

pLisp :: Par t -> Par (Lisp t)
pLisp p
  =   (iden >>= pAtom p)
  <|> id <$ punc "[" <* spc <*> pCdr p <* spc <* punc "]"
  <|> I <$ punc "{" <* spc <*> pPoint <* spc <* punc "}"
  <|> E <$ punc "(" <* spc <*> p <* spc <* punc ")"

pAtom :: Par t -> String -> Par (Lisp t)
pAtom p x
  =   (x :.) <$ spc <* punc "." <* spc <*> pLoc (bindX x) (pLisp p)
  <|> (x :!) <$ spc <* punc "|" <* spc <*> pLoc (bindI x) (pLisp p)
  <|> pure (A x)

pCdr :: Par t -> Par (Lisp t)
pCdr p
  =   id <$ punc "," <* spc <*> pLisp p
  <|> (:&) <$> pLisp p <* spc <*> pCdr p
  <|> pure (A "")

instance Disp t => Disp (Lisp t) where
  disp e (A "") = "[]"
  disp e (A x) = x
  disp e (a :& d) = "[" ++ disp e a ++ cdr d where
    cdr (A "") = "]"
    cdr (a :& d) = " " ++ disp e a ++ cdr d
    cdr d = ", " ++ disp e d ++ "]"
  disp e (x :. b) = n ++ "." ++ disp (e {termDisp = termDisp e :< n}) b where
    n = freshen (termDisp e) x
  disp e (x :! b) = n ++ "|" ++ disp (e {termDisp = intvDisp e :< n}) b where
    n = freshen (intvDisp e) x
  disp e (I p) = "{" ++ disp e p ++ "}"
  disp e (E t) = "(" ++ disp e t ++ ")"

instance Disp t => Show (Lisp t) where
  show = dispShow
