module Basics where

data Zero : Set where

record One : Set where constructor <>

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
infixr 4 _,_

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _*_

the : (X : Set) -> X -> X
the X x = x

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}

reff : {X : Set}(x : X) -> x == x
reff x = refl

_=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
        f == f' -> x == x' -> f x == f' x'
refl =$= refl = refl

_$=_ : {S : Set}{T : Set}
       (f : S -> T) ->
       {x y : S} -> x == y ->
       f x == f y
f $= q = refl =$= q

_=$_ : {S : Set}{T : S -> Set}{f g : (x : S) -> T x} ->
       (f == g) -> (x : S) -> f x == g x
refl =$ x = refl

_=$: : {X Y : Set}{f f' : .X -> Y}{x x' : X} ->
        f == f' -> f x == f' x'
refl =$: = refl

infixl 20 _=$=_ _$=_ _=$_ _=$:

sym : {X : Set}{x y : X} -> x == y -> y == x
sym refl = refl

_[QED] : {X : Set}(x : X) -> x == x
x [QED] = refl

_=[_>=_ : {X : Set}(x : X){y z : X} -> x == y -> y == z -> x == z
x =[ refl >= q = q

_=<_]=_ : {X : Set}(x : X){y z : X} -> y == x -> y == z -> x == z
x =< refl ]= q = q

infixr 10 _=[_>=_ _=<_]=_
infixr 11 _[QED]

data Nat : Set where
  ze : Nat
  _su : Nat -> Nat
infixl 7 _su
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
n +N ze = n
n +N (m su) = n +N m su
infixl 7 _+N_

data Dec (X : Set) : Set where
  yes : X -> Dec X
  no  : (X -> Zero) -> Dec X

