{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
    StandaloneDeriving,
    FlexibleInstances, FlexibleContexts, UndecidableInstances #-}

module Lisp where

import Control.Applicative
import Data.Void

import Bwd
import Intv
import Disp
import Par
import Bind
import Thin

data Lisp br pa x
  = A String
  | Lisp br pa x :& Lisp br pa x
  | String :. B (Lisp br pa) x
  | P (Point x)
  | Pa (pa (Lisp br pa) x)
  | Br (br (Lisp br pa) x)

pLisp :: Par (br (Lisp br pa) LI) -> Par (pa (Lisp br pa) LI) ->
         Par (Lisp br pa LI)
pLisp br pa
  =   (iden >>= pAtom br pa)
  <|> id <$ punc "[" <* spc <*> pCdr br pa <* spc <* punc "]"
  <|> P  <$ punc "<" <* spc <*> pPoint <* spc <* punc ">"
  <|> Pa <$ punc "(" <* spc <*> pa <* spc <* punc ")"
  <|> Br <$ punc "{" <* spc <*> br <* spc <* punc "}"
  
pAtom :: Par (br (Lisp br pa) LI) -> Par (pa (Lisp br pa) LI) ->
         String -> Par (Lisp br pa LI)
pAtom br pa x
  =   (x :.) <$ spc <* punc "." <* spc
        <*> (B <$> pLoc (bindInx x) (pLisp br pa))
  <|> pure (A x)

pCdr :: Par (br (Lisp br pa) LI) -> Par (pa (Lisp br pa) LI) ->
        Par (Lisp br pa LI)
pCdr br pa
  =   id <$ punc "," <* spc <*> pLisp br pa
  <|> (:&) <$> pLisp br pa <* spc <*> pCdr br pa
  <|> pure (A "")

instance (Disp (br (Lisp br pa) LI), Disp (pa (Lisp br pa) LI))
  => Disp (Lisp br pa LI) where
  disp e (A "") = "[]"
  disp e (A x) = x
  disp e (a :& d) = "[" ++ disp e a ++ cdr d where
    cdr (A "") = "]"
    cdr (a :& d) = " " ++ disp e a ++ cdr d
    cdr d = ", " ++ disp e d ++ "]"
  disp e (x :. B b) = n ++ "." ++ disp e' b where
    (e', n) = freshen e x
  disp e (P p)  = "<" ++ disp e p ++ ">"
  disp e (Pa t) = "(" ++ disp e t ++ ")"
  disp e (Br t) = "{" ++ disp e t ++ "}"

instance (Disp (br (Lisp br pa) LI), Disp (pa (Lisp br pa) LI))
  => Show (Lisp br pa LI) where
  show = dispShow


deriving instance (Functor (br (Lisp br pa)), Functor (pa (Lisp br pa)))
  => Functor (Lisp br pa)
deriving instance (Foldable (br (Lisp br pa)), Foldable (pa (Lisp br pa)))
  => Foldable (Lisp br pa)
deriving instance (Traversable (br (Lisp br pa)), Traversable (pa (Lisp br pa)))
  => Traversable (Lisp br pa)

instance (DeBruijn (br (Lisp br pa)), DeBruijn (pa (Lisp br pa)))
  => DeBruijn (Lisp br pa) where
  deBruijn f i (A x) = pure (A x)
  deBruijn f i (a :& d) = (:&) <$> deBruijn f i a <*> deBruijn f i d
  deBruijn f i (x :. b) = (x :.) <$> deBruijn f i b
  deBruijn f i (P p) = P <$> deBruijn f i p
  deBruijn f i (Pa t) = Pa <$> deBruijn f i t
  deBruijn f i (Br t) = Br <$> deBruijn f i t
