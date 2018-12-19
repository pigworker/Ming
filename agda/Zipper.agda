module Zipper where

open import Basics
open import Thinning
open import Term

data Term' (m : Nat) : Nat -> Dir -> Set where
  hole  : Term' m m syn
  _<,_  : {n : Nat} -> Term' m n chk -> Term m chk -> Term' m n chk
  _,>_  : {n : Nat} -> Term m chk -> Term' m n chk -> Term' m n chk
  !_    : {n : Nat} -> Term' (m su) n chk -> Term' m n chk
  [_]   : {n : Nat} -> Term' m n syn -> Term' m n chk
  _<::_ : {n : Nat} -> Term' m n chk -> Term m chk -> Term' m n syn
  _::>_ : {n : Nat} -> Term m chk -> Term' m n chk -> Term' m n syn
  _</_  : {n : Nat} -> Term' m n syn -> Term m chk -> Term' m n syn
  _/>_  : {n : Nat} -> Term m syn -> Term' m n chk -> Term' m n syn

oterm' : forall {m n d} -> Term' m n d -> m <= n
oterm' hole = oi
oterm' (t' <, _) = oterm' t'
oterm' (_ ,> t') = oterm' t'
oterm' (! t') = opred (oterm' t') -- oi o' - oterm' t'
oterm' [ t' ] = oterm' t'
oterm' (t' <:: _) = oterm' t'
oterm' (_ ::> t') = oterm' t'
oterm' (t' </ _) = oterm' t'
oterm' (_ /> t') = oterm' t'

_+T_ : forall {m n d} -> Term' m n d -> Term n syn -> Term m d
hole       +T f = f
(s' <, t)  +T f = (s' +T f) , t
(s ,> t')  +T f = s , (t' +T f)
(! t')     +T f = ! (t' +T f)
[ t' ]     +T f = [ t' +T f ]
(t' <:: T) +T f = (t' +T f) :: T
(t ::> T') +T f = t :: (T' +T f)
(e' </ s)  +T f = (e' +T f) / s
(e /> s')  +T f = e / (s' +T f)

