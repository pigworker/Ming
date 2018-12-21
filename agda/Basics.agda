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

data Mebbe (X : Set) : Set where
  aye : X -> Mebbe X
  naw : Mebbe X

_>>=_ : {A B : Set} -> Mebbe A -> (A -> Mebbe B) -> Mebbe B
aye a >>= k = k a
naw   >>= _ = naw

id : {X : Set} -> X -> X
id x = x

_`_ : forall {R S T : Set} -> (S -> T) -> (R -> S) -> R -> T
(f ` g) r = f (g r)

the : (X : Set) -> X -> X
the X x = x

data _==_ {l}{X : Set l}(x : X) : X -> Set where
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

data Bwd (X : Set) : Set where
  [] : Bwd X
  _&_ : Bwd X -> X -> Bwd X

_+B_ : forall {X} -> Bwd X -> Bwd X -> Bwd X
xz +B [] = xz
xz +B (yz & x) = xz +B yz & x
infixl 3 _&_ _+B_

data El {X : Set}(x : X) : Bwd X -> Set where
  ze : {xz : Bwd X} -> El x (xz & x)
  _su : {xz : Bwd X}{y : X} -> El x xz -> El x (xz & y)

data BVec (X : Set) : Nat -> Set where
  [] : BVec X ze
  _&_ : {n : Nat} -> BVec X n -> X -> BVec X (n su)

_+V_ : forall {X}{n m : Nat} -> BVec X n -> BVec X m -> BVec X (n +N m)
xz +V [] = xz
xz +V (yz & x) = (xz +V yz) & x

pure : {n : Nat}{X : Set} -> X -> BVec X n
pure {ze} x = []
pure {n su} x = pure x & x

_<*>_ : {n : Nat}{S T : Set} -> BVec (S -> T) n -> BVec S n -> BVec T n
[] <*> [] = []
(fz & f) <*> (sz & s) = (fz <*> sz) & f s
infixl 2 _<*>_

bVecIdentity : forall {n X}(f : X -> X)(q : (x : X) -> f x == x)(xz : BVec X n) -> (pure f <*> xz) == xz
bVecIdentity f q [] = refl
bVecIdentity f q (xz & x) = reff _&_ =$= bVecIdentity f q xz =$= q x

bVecComposition : forall {n R S T}
  (fz : BVec (S -> T) n)(gz : BVec (R -> S) n)(xz : BVec R n) ->
  (fz <*> (gz <*> xz)) == (pure _`_ <*> fz <*> gz <*> xz)
bVecComposition [] [] [] = refl
bVecComposition (fz & f) (gz & g) (xz & x) = (_& _) $= bVecComposition fz gz xz

bVecHomomorphism : forall {n S T}(f : S -> T)(s : S) ->
  (pure {n} f <*> pure s) == pure (f s)
bVecHomomorphism {ze} f s = refl
bVecHomomorphism {n su} f s = (_& _) $= bVecHomomorphism f s

bVecInterchange : forall {n S T}(fz : BVec (S -> T) n)(s : S) ->
  (fz <*> pure s) == (pure (\ f -> f s) <*> fz)
bVecInterchange [] s = refl
bVecInterchange (fz & f) s = (_& _) $= bVecInterchange fz s

bVecMapMap : forall {n R S T}(f : S -> T)(g : R -> S)(rz : BVec R n) ->
  (pure f <*> (pure g <*> rz)) == (pure (f ` g) <*> rz)
bVecMapMap f g rz =
  (pure f <*> (pure g <*> rz))
    =[ bVecComposition (pure f) (pure g) rz >=
  (pure _`_ <*> pure f <*> pure g <*> rz)
    =[ (\ z -> z <*> pure g <*> rz) $= bVecHomomorphism _`_ f >=
  (pure (\ h r -> f (h r)) <*> pure g <*> rz)
    =[ (_<*> rz) $= bVecHomomorphism (\ h r -> f (h r)) g  >=
  (pure (f ` g) <*> rz)
    [QED]

bVecMapExt : forall {n S T}(f g : S -> T)(q : (s : S) -> f s == g s) ->
             (sz : BVec S n) -> (pure f <*> sz) == (pure g <*> sz)
bVecMapExt f g q [] = refl
bVecMapExt f g q (sz & s) = reff _&_ =$= bVecMapExt f g q sz =$= q s

bVecMapCat : forall {S T}(f : S -> T){n m}(xz : BVec S n)(yz : BVec S m) ->
  (pure f <*> (xz +V yz)) == ((pure f <*> xz) +V (pure f <*> yz))
bVecMapCat f xz [] = refl
bVecMapCat f xz (yz & y) = reff _&_ =$= bVecMapCat f xz yz =$ f y

data App' (n : Nat)(X : Set) : Set1 where
  pure' : X -> App' n X
  _<*>'_ : forall {S} -> App' n (S -> X) -> App' n S -> App' n X
  <_> : BVec X n -> App' n X
infixl 2 _<*>'_

app' : forall {n X}(xn : App' n X) -> BVec X n
app' (pure' x) = pure x
app' (fa <*>' sa) = app' fa <*> app' sa
app' < xz > = xz

data AppN' (n : Nat)(X : Set) : Set1 where
  pure' : X -> AppN' n X
  _<*>'_ : forall {S} -> AppN' n (S -> X) -> BVec S n -> AppN' n X

appN' : forall {n X}(xn : AppN' n X) -> BVec X n
appN' (pure' x) = pure x
appN' (fn <*>' sz) = appN' fn <*> sz

appCat : forall {n S T U} -> (S -> T -> U) -> AppN' n S -> AppN' n T -> AppN' n U
appCat f sn (tn <*>' xz) = appCat (\ s g t -> f s (g t)) sn tn <*>' xz
appCat f (pure' s) (pure' t) = pure' (f s t)
appCat f (sn <*>' xz) (pure' t) = appCat (\ g t s -> f (g s) t) sn (pure' t) <*>' xz

appCatLemma : forall {n S T U}(f : S -> T -> U)(sn : AppN' n S)(tn : AppN' n T) ->
  appN' (appCat f sn tn) == (pure f <*> appN' sn <*> appN' tn)
appCatLemma f sn (tn <*>' xz) =
  (appN' (appCat (\ s g t -> f s (g t)) sn tn) <*> xz)
    =[ (_<*> xz) $= appCatLemma _ sn tn >=
  (pure (\ s g t -> f s (g t)) <*> appN' sn <*> appN' tn <*> xz)
    =< (\ z -> z <*> appN' tn <*> xz) $= bVecMapMap _`_ f (appN' sn) ]=
  (pure _`_ <*> (pure f <*> appN' sn) <*> appN' tn <*> xz)
    =< bVecComposition (pure f <*> appN' sn) (appN' tn) xz ]=
  (pure f <*> appN' sn <*> (appN' tn <*> xz))
    [QED]
appCatLemma f (pure' y) (pure' x) =
  pure (f y x)
    =< bVecHomomorphism (f y) x ]=
  (pure (f y) <*> pure x)
    =< (_<*> pure x) $= bVecHomomorphism f y ]=
  (pure f <*> pure y <*> pure x)
    [QED]
appCatLemma f (sn <*>' xz) (pure' t) =
  (appN' (appCat (\ g t s -> f (g s) t) sn (pure' t)) <*> xz)
    =[ (_<*> xz) $= appCatLemma (\ g t s -> f (g s) t) sn (pure' t) >=
  (pure (\ g t s -> f (g s) t) <*> appN' sn <*> appN' (pure' t) <*> xz)
    =[ (_<*> xz) $= bVecInterchange (pure (\ g t s -> f (g s) t) <*> appN' sn) t >=
  (pure (\ h -> h t) <*> (pure (\ g t s -> f (g s) t) <*> appN' sn) <*> xz)
    =[ (_<*> xz) $= bVecMapMap  (\ h -> h t) (\ g t s -> f (g s) t) (appN' sn) >=
  (pure (\ r s -> f (r s) t) <*> appN' sn <*> xz)
    =< (\ z -> z <*> appN' sn <*> xz) $= bVecHomomorphism (\ h g r -> h (g r))(\ r -> f r t) ]=
  (pure (\ h g r -> h (g r)) <*> pure (\ r -> f r t) <*> appN' sn <*> xz)
    =< bVecComposition (pure (\ r -> f r t)) (appN' sn) xz  ]=
  (pure (\ r -> f r t) <*> (appN' sn <*> xz))
    =< bVecMapMap (\ h -> h t) f (appN' sn <*> xz) ]=
  (pure (\ h -> h t) <*> (pure f <*> (appN' sn <*> xz)))
    =< bVecInterchange (pure f <*> (appN' sn <*> xz)) t ]=
  (pure f <*> (appN' sn <*> xz) <*> pure t)
    [QED]

appNorm : forall {n X} -> App' n X -> AppN' n X
appNorm (pure' x) = pure' x
appNorm (f <*>' s) = appCat id (appNorm f) (appNorm s)
appNorm < xz > = pure' id <*>' xz

appNormLemma : forall {n X}(xa : App' n X) -> app' xa == appN' (appNorm xa)
appNormLemma (pure' x) = refl
appNormLemma (fa <*>' sa)
  rewrite appCatLemma id (appNorm fa) (appNorm sa)
        | bVecIdentity id (\ _ -> refl) (appN' (appNorm fa))
        = reff _<*>_ =$= appNormLemma fa =$= appNormLemma sa
appNormLemma < xz > = sym (bVecIdentity id (\ _ -> refl) xz)

applicatives : forall {n X}(xa0 xa1 : App' n X) -> appNorm xa0 == appNorm xa1 -> app' xa0 == app' xa1
applicatives xa0 xa1 q
  rewrite appNormLemma xa0
        | appNormLemma xa1
        | q
        = refl

Pi : (S : Set)(T : S -> Set) -> Set
Pi S T = (x : S) -> T x

data BAll {X}(P : X -> Set) : Bwd X -> Set where
  [] : BAll P []
  _&_ : forall {xz x} -> BAll P xz -> P x -> BAll P (xz & x)

bAll : forall {X}{P Q : X -> Set} -> ({x : X} -> P x -> Q x) -> {xz : Bwd X} -> BAll P xz -> BAll Q xz
bAll f [] = []
bAll f (pz & p) = bAll f pz & f p

aproj : forall {X}{P : X -> Set}{xz x} -> El x xz -> BAll P xz -> P x
aproj ze (pz & p) = p
aproj (i su) (pz & p) = aproj i pz

aprojbAll : forall {X}{P Q : X -> Set}{xz x}(i : El x xz)(pz : BAll P xz)
  (f : {x : X} -> P x -> Q x) ->
  aproj i (bAll f pz) == (f (aproj i pz))
aprojbAll ze (pz & p) f = refl
aprojbAll (i su) (pz & p) f = aprojbAll i pz f

_+A_ : forall {X}{P}{xz yz : Bwd X} -> BAll P xz -> BAll P yz -> BAll P (xz +B yz)
pz +A [] = pz
pz +A (qz & p) = pz +A qz & p
infixl 3 _+A_

