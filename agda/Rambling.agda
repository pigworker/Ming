module Rambling where

record One : Set where constructor <>

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg

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

data Zero : Set where

data Nat : Set where
  ze : Nat
  _su : Nat -> Nat
infixl 7 _su
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
n +N ze = n
n +N (m su) = n +N m su
infixl 7 _+N_

data _<=_ : Nat -> Nat -> Set where
  _o' : {n m : Nat} -> n <= m -> n <= m su
  _os : {n m : Nat} -> n <= m -> n su <= m su
  oz : ze <= ze
infix 5 _<=_
infixr 7 _o' _os

domo : {n m : Nat}(th : n <= m) -> Nat
domo {n} th = n

oi : {n : Nat} -> n <= n
oi {ze} = oz
oi {_ su} = oi os

oe : {n : Nat} -> ze <= n
oe {ze} = oz
oe {_ su} = oe o'

oe! : {n : Nat}(x y : ze <= n) -> x == y
oe! (x o') (y o') rewrite oe! x y = refl
oe! oz oz = refl

_-_ : {p n m : Nat} -> p <= n -> n <= m -> p <= m
th    - ph o' = (th - ph) o'
th o' - ph os = (th - ph) o'
th os - ph os = (th - ph) os
oz    - oz    = oz
infixl 5 _-_

_-oi : {n m : Nat}(th : n <= m) -> (th - oi) == th
(th o') -oi rewrite th -oi = refl
(th os) -oi rewrite th -oi = refl
oz -oi = refl

_-[_-_] : {q p n m : Nat}(th : q <= p)(ph : p <= n)(ps : n <= m) ->
          (th - (ph - ps)) == ((th - ph) - ps)
th -[ ph - ps o' ] rewrite th -[ ph - ps ] = refl
th -[ ph o' - ps os ] rewrite th -[ ph - ps ] = refl
(th o') -[ ph os - ps os ] rewrite th -[ ph - ps ] = refl
(th os) -[ ph os - ps os ] rewrite th -[ ph - ps ] = refl
oz -[ oz - oz ] = refl

miss : {n m : Nat} -> n <= m -> Nat
miss (th o') = miss th su
miss (th os) = miss th
miss oz = ze

not : {n m : Nat}(th : n <= m) -> miss th <= m
not (th o') = not th os
not (th os) = not th o'
not oz = oz

notLemma : {n m : Nat}(th : n <= m)(y : 1 <= n)(x : 1 <= miss th) ->
           (y - th) == (x - not th) -> Zero
notLemma (th o') y (x o') q with y - th | notLemma th y x
notLemma (th o') y (x o') refl | .(x - not th) | b = b refl
notLemma (th o') y (x os) ()
notLemma (th os) (y o') x q with y - th | notLemma th y x
notLemma (th os) (y o') x refl | .(x - not th) | b = b refl
notLemma (th os) (y os) x ()
notLemma oz ()

opred : {n m : Nat}(th : n su <= m) -> n <= m
opred (th o') = opred th o'
opred (th os) = th o'

opredLemma : {p n m : Nat}(th : p <= n)(ph : n su <= m) ->
   (th o' - ph) == (th - opred ph)
opredLemma th (ph o') rewrite opredLemma th ph = refl
opredLemma th (ph os) = refl

_+th_ : forall {n m n' m'}(th : n <= m)(ph : n' <= m') -> (n +N n') <= (m +N m')
th +th (ph o') = th +th ph o'
th +th (ph os) = th +th ph os
th +th oz = th
infixl 7 _+th_

oi+thoi : forall n m -> (oi {n} +th oi {m}) == oi {n +N m}
oi+thoi n ze = refl
oi+thoi n (m su) rewrite oi+thoi n m = refl

[_-_]+th[_-_] : forall {p n m p' n' m'}
  (th : p <= n)(ph : n <= m)
  (th' : p' <= n')(ph' : n' <= m') ->
  ((th - ph) +th (th' - ph')) == ((th +th th') - (ph +th ph'))
[ th - ph ]+th[ th' - ph' o' ] rewrite [ th - ph ]+th[ th' - ph' ] = refl
[ th - ph ]+th[ th' o' - ph' os ] rewrite [ th - ph ]+th[ th' - ph' ] = refl
[ th - ph ]+th[ th' os - ph' os ] rewrite [ th - ph ]+th[ th' - ph' ] = refl
[ th - ph ]+th[ oz - oz ] = refl

data Tri : {p n m : Nat}(th : p <= n)(ph : n <= m)(ps : p <= m) -> Set where
  _t-'' : {p n m : Nat}{th : p <= n}{ph : n <= m}{ps : p <= m} ->
          Tri th ph ps -> Tri th (ph o') (ps o')
  _t's' : {p n m : Nat}{th : p <= n}{ph : n <= m}{ps : p <= m} ->
          Tri th ph ps -> Tri (th o') (ph os) (ps o')
  _tsss : {p n m : Nat}{th : p <= n}{ph : n <= m}{ps : p <= m} ->
          Tri th ph ps -> Tri (th os) (ph os) (ps os)
  tzzz  : Tri oz oz oz
infixl 7 _t-'' _t's' _tsss

_+Tri_ : {p n m : Nat}{th : p <= n}{ph : n <= m}{ps : p <= m}(x : Tri th ph ps)
         {p' n' m' : Nat}{th' : p' <= n'}{ph' : n' <= m'}{ps' : p' <= m'}(y : Tri th' ph' ps')
         ->
         Tri (th +th th') (ph +th ph') (ps +th ps')
x +Tri (y t-'') = (x +Tri y) t-''
x +Tri (y t's') = (x +Tri y) t's'
x +Tri (y tsss) = (x +Tri y) tsss
x +Tri tzzz = x

mkTri : {p n m : Nat}(th : p <= n)(ph : n <= m) -> Tri th ph (th - ph)
mkTri th (ph o') = mkTri th ph t-''
mkTri (th o') (ph os) = mkTri th ph t's'
mkTri (th os) (ph os) = mkTri th ph tsss
mkTri oz oz = tzzz

triDet : {p n m : Nat}{th : p <= n}{ph : n <= m}{ps ps' : p <= m} ->
          Tri th ph ps -> Tri th ph ps' -> ps == ps'
triDet (a t-'') (b t-'') rewrite triDet a b = refl
triDet (a t's') (b t's') rewrite triDet a b = refl
triDet (a tsss) (b tsss) rewrite triDet a b = refl
triDet tzzz tzzz = refl

triMono : {p n m : Nat}{th th' : p <= n}{ph : n <= m}{ps : p <= m} ->
           Tri th ph ps -> Tri th' ph ps -> th == th'
triMono (a t-'') (b t-'') rewrite triMono a b = refl
triMono (a t's') (b t's') rewrite triMono a b = refl
triMono (a tsss) (b tsss) rewrite triMono a b = refl
triMono tzzz tzzz = refl

trioi : {n m : Nat}(th : n <= m) -> Tri th oi th
trioi (th o') = trioi th t's'
trioi (th os) = trioi th tsss
trioi oz = tzzz

pullback : forall {n0 n1 m}(th : n0 <= m)(ph : n1 <= m) ->
           Sg Nat \ p -> Sg (p <= n0) \ th' -> Sg (p <= n1) \ ph' -> Sg (p <= m) \ ps ->
           Tri th' th ps * Tri ph' ph ps
pullback (th o') (ph o') = let _ , _ , _ , _ , a , b = pullback th ph in _ , _ , _ , _ , a t-'' , b t-''
pullback (th o') (ph os) = let _ , _ , _ , _ , a , b = pullback th ph in _ , _ , _ , _ , a t-'' , b t's'
pullback (th os) (ph o') = let _ , _ , _ , _ , a , b = pullback th ph in _ , _ , _ , _ , a t's' , b t-''
pullback (th os) (ph os) = let _ , _ , _ , _ , a , b = pullback th ph in _ , _ , _ , _ , a tsss , b tsss
pullback oz oz = _ , _ , _ , _ , tzzz , tzzz

isPullback : forall {n0 n1 m}{th : n0 <= m}{ph : n1 <= m} ->
  let p , th' , ph' , ps , a , b = pullback th ph
  in  forall {p0}{th0 : p0 <= n0}{ph0 : p0 <= n1}{ps0 : p0 <= m}
        (c : Tri th0 th ps0)(d : Tri ph0 ph ps0) ->
        Sg (p0 <= p) \ ps1 -> Tri ps1 th' th0 * Tri ps1 ps ps0 * Tri ps1 ph' ph0
isPullback (c t-'') (d t-'') = let _ , e , f , g = isPullback c d in _ , e , f t-'' , g
isPullback (c t-'') (d t's') = let _ , e , f , g = isPullback c d in _ , e , f t-'' , g t-''
isPullback (c t's') (d t-'') = let _ , e , f , g = isPullback c d in _ , e t-'' , f t-'' , g
isPullback (c t's') (d t's') = let _ , e , f , g = isPullback c d in _ , e t's' , f t's' , g t's'
isPullback (c tsss) (d tsss) = let _ , e , f , g = isPullback c d in _ , e tsss , f tsss , g tsss
isPullback tzzz tzzz = oz , tzzz , tzzz , tzzz

pullbackoi : {n : Nat} -> pullback (oi {n}) oi == (n , oi , oi , oi , trioi oi , trioi oi)
pullbackoi {ze} = refl
pullbackoi {n su} with pullback (oi {n}) (oi {n}) | pullbackoi {n}
pullbackoi {n su} | .(n , oi , oi , oi , trioi oi , trioi oi) | refl = refl

pullback+Lemma : {n0 n1 m n0z n1z mz : Nat}
                 (th : n0 <= m)(ph : n1 <= m)
                 (thz : n0z <= mz)(phz : n1z <= mz) ->
                 let p , th' , ph' , ps , a , b = pullback th ph
                     pz , thz' , phz' , psz , az , bz = pullback thz phz
                 in  pullback (th +th thz) (ph +th phz) ==
                     (p +N pz , th' +th thz' , ph' +th phz' , ps +th psz ,
                       a +Tri az , b +Tri bz)
pullback+Lemma th ph (thz o') (phz o') rewrite pullback+Lemma th ph thz phz = refl
pullback+Lemma th ph (thz o') (phz os) rewrite pullback+Lemma th ph thz phz = refl
pullback+Lemma th ph (thz os) (phz o') rewrite pullback+Lemma th ph thz phz = refl
pullback+Lemma th ph (thz os) (phz os) rewrite pullback+Lemma th ph thz phz = refl
pullback+Lemma th ph oz oz = refl

{-
data Parti : {p n m : Nat} -> p <= m -> n <= m -> Set where
  _ps' : {p n m : Nat}{th : p <= m}{ph : n <= m} ->
         Parti th ph -> Parti (th os) (ph o')
  _p's : {p n m : Nat}{th : p <= m}{ph : n <= m} ->
         Parti th ph -> Parti (th o') (ph os)
  pzz  : Parti oz oz
infixr 7 _ps' _p's

oparti : {n m : Nat}(th : n <= m) -> Parti th (not th)
oparti (th o') = oparti th p's
oparti (th os) = oparti th ps'
oparti oz = pzz
-}

data Elem? {n m : Nat}(th : n <= m) : 1 <= m -> Set where
  yes : (x : 1 <= n) -> Elem? th (x - th)
  no  : (x : 1 <= miss th) -> Elem? th (x - not th)

elem? : {n m : Nat}(th : n <= m)(x : 1 <= m) -> Elem? th x
elem? (th o') (x o') with elem? th x
elem? (th o') (.(x - th) o') | yes x = yes x
elem? (th o') (.(x - not th) o') | no x = no (x o')
elem? (th o') (x os) with oe! x (oe - not th)
elem? (th o') (.(oe - not th) os) | refl = no (oe os)
elem? (th os) (x o') with elem? th x
elem? (th os) (.(x - th) o') | yes x = yes (x o')
elem? (th os) (.(x - not th) o') | no x = no x
elem? (th os) (x os) with oe! x (oe - th)
elem? (th os) (.(oe - th) os) | refl = yes (oe os)
elem? oz ()

elemLemma : {n m : Nat}(th : n <= m)(x : 1 <= n) -> elem? th (x - th) == yes x
elemLemma (th o') x rewrite elemLemma th x = refl
elemLemma (th os) (x o') rewrite elemLemma th x = refl
elemLemma (th os) (x os) with oe! x oe
elemLemma (th os) (.oe os) | refl with oe! (oe - th) (oe - th)
elemLemma (th os) (.oe os) | refl | refl = refl
elemLemma oz ()


data Atom : Set where
  nil : Atom

data Dec (X : Set) : Set where
  yes : X -> Dec X
  no  : (X -> Zero) -> Dec X

atomEq? : (x y : Atom) -> Dec (x == y)
atomEq? nil nil = yes refl

atomEqLemma : (x : Atom) -> atomEq? x x == yes refl
atomEqLemma nil = refl

data Pat (m : Nat) : Set where
  $    : Atom -> Pat m
  _,_  : Pat m -> Pat m -> Pat m
  !_   : Pat (m su) -> Pat m
  [?_] : {n : Nat} -> n <= m -> Pat m
  ><   : Pat m
infixr 4 _,_
infixr 3 !_

data Dir : Set where chk syn : Dir

data Term (m : Nat) : Dir -> Set where
  $    : Atom -> Term m chk
  _,_  : Term m chk -> Term m chk -> Term m chk
  !_   : Term (m su) chk -> Term m chk
  [_]  : Term m syn -> Term m chk
  _::_ : Term m chk -> Term m chk -> Term m syn
  #_   : 1 <= m -> Term m syn
  _/_  : Term m syn -> Term m chk -> Term m syn
infixl 5 _/_ _::_
infix 6 #_

TermNoConfStmt : forall {m d}(t0 t1 : Term m d) -> Set -> Set
TermNoConfStmt ($ x0) ($ x1) P = x0 == x1 -> P
TermNoConfStmt ($ x) (_ , _) P = One
TermNoConfStmt ($ x) (! _) P = One
TermNoConfStmt ($ x) [ _ ] P = One
TermNoConfStmt (t0 , t1) ($ x) P = One
TermNoConfStmt (s0 , t0) (s1 , t1) P = s0 == s1 -> t0 == t1 -> P
TermNoConfStmt (t0 , t1) (! t2) P = One
TermNoConfStmt (t0 , t1) [ t2 ] P = One
TermNoConfStmt (! t0) ($ x) P = One
TermNoConfStmt (! t0) (t1 , t2) P = One
TermNoConfStmt (! t0) (! t1) P = t0 == t1 -> P
TermNoConfStmt (! t0) [ t1 ] P = One
TermNoConfStmt [ t0 ] ($ x) P = One
TermNoConfStmt [ t0 ] (t1 , t2) P = One
TermNoConfStmt [ t0 ] (! t1) P = One
TermNoConfStmt [ e0 ] [ e1 ] P = e0 == e1 -> P
TermNoConfStmt (t0 :: T0) (t1 :: T1) P = t0 == t1 -> T0 == T1 -> P
TermNoConfStmt (t0 :: t1) (# x) P = One
TermNoConfStmt (t0 :: t1) (t2 / t3) P = One
TermNoConfStmt (# x) (t1 :: t2) P = One
TermNoConfStmt (# x0) (# x1) P = x0 == x1 -> P
TermNoConfStmt (# x) (t1 / t2) P = One
TermNoConfStmt (t0 / t1) (t2 :: t3) P = One
TermNoConfStmt (t0 / t1) (# x) P = One
TermNoConfStmt (e0 / s0) (e1 / s1) P = e0 == e1 -> s0 == s1 -> P

termNoConf : forall {m d}(t0 t1 : Term m d) -> t0 == t1 -> {P : Set} -> TermNoConfStmt t0 t1 P -> P
termNoConf ($ x) .($ x) refl p = p refl
termNoConf (t0 , t1) .(t0 , t1) refl p = p refl refl
termNoConf (! t0) .(! t0) refl p = p refl
termNoConf [ t0 ] .([ t0 ]) refl p = p refl
termNoConf (t0 :: t1) .(t0 :: t1) refl p = p refl refl
termNoConf (# x) .(# x) refl p = p refl
termNoConf (t0 / t1) .(t0 / t1) refl p = p refl refl

_^T_ : {n m : Nat}{d : Dir} -> Term n d -> n <= m -> Term m d
$ x      ^T th = $ x
(s , t)  ^T th = s ^T th , t ^T th 
(! t)    ^T th = ! t ^T th os
[ e ]    ^T th = [ e ^T th ]
(t :: T) ^T th = t ^T th :: T ^T th
(# x)    ^T th = # (x - th)
(e / s)  ^T th = e ^T th / s ^T th
infixl 6 _^T_

_^Toi : {n : Nat}{d : Dir}(t : Term n d) -> (t ^T oi) == t
$ x ^Toi = refl
(s , t) ^Toi rewrite s ^Toi | t ^Toi = refl
(! t) ^Toi rewrite t ^Toi = refl
[ e ] ^Toi rewrite e ^Toi = refl
(t :: T) ^Toi rewrite t ^Toi | T ^Toi = refl
(# x) ^Toi rewrite x -oi = refl
(e / s) ^Toi rewrite e ^Toi | s ^Toi = refl

_^T[_-_] : {p n m : Nat}{d : Dir}(t : Term p d)(th : p <= n)(ph : n <= m) ->
  (t ^T (th - ph)) == ((t ^T th) ^T ph)
$ x ^T[ th - ph ] = refl
(s , t) ^T[ th - ph ] rewrite s ^T[ th - ph ] | t ^T[ th - ph ] = refl
(! t) ^T[ th - ph ] rewrite t ^T[ th os - ph os ] = refl
[ e ] ^T[ th - ph ] rewrite e ^T[ th - ph ] = refl
(t :: T) ^T[ th - ph ] rewrite t ^T[ th - ph ] | T ^T[ th - ph ] = refl
(# x) ^T[ th - ph ] rewrite x -[ th - ph ] = refl
(e / s) ^T[ th - ph ] rewrite e ^T[ th - ph ] | s ^T[ th - ph ] = refl

thinPullback : {n0 n1 m : Nat}{d : Dir}
  (t0 : Term n0 d)(th : n0 <= m)(t1 : Term n1 d)(ph : n1 <= m) ->
  (t0 ^T th) == (t1 ^T ph) ->
  let p , th' , ph' , _ = pullback th ph
  in  Sg (Term p d) \ t -> ((t ^T th') == t0) * ((t ^T ph') == t1)
thinPullback ($ x) th ($ .x) ph refl = $ x , refl , refl
thinPullback ($ x) th (t1 , t2) ph ()
thinPullback ($ x) th (! t1) ph ()
thinPullback ($ x) th [ t1 ] ph ()
thinPullback (t0 , t1) th ($ x) ph ()
thinPullback (ta0 , td0) th (ta1 , td1) ph q = termNoConf _ _ q \ qa qd ->
  let ta , aq0 , aq1 = thinPullback ta0 th ta1 ph qa
      td , dq0 , dq1 = thinPullback td0 th td1 ph qd
  in  (ta , td) , reff _,_ =$= aq0 =$= dq0 , reff _,_ =$= aq1 =$= dq1
thinPullback (t0 , t1) th (! t2) ph ()
thinPullback (t0 , t1) th [ t2 ] ph ()
thinPullback (! t0) th ($ x) ph ()
thinPullback (! t0) th (t1 , t2) ph ()
thinPullback (! t0) th (! t1) ph q = termNoConf _ _ q \ q' -> 
  let t , q0 , q1 = thinPullback t0 (th os) t1 (ph os) q' in (! t) , !_ $= q0 , !_ $= q1 
thinPullback (! t0) th [ t1 ] ph ()
thinPullback [ t0 ] th ($ x) ph ()
thinPullback [ t0 ] th (t1 , t2) ph ()
thinPullback [ t0 ] th (! t1) ph ()
thinPullback [ e0 ] th [ e1 ] ph q = termNoConf _ _ q \ eq ->
  let e , eq0 , eq1 = thinPullback e0 th e1 ph eq in [ e ] , [_] $= eq0 , [_] $= eq1
thinPullback (t0 :: T0) th (t1 :: T1) ph q = termNoConf _ _ q \ qt qT ->
  let t , tq0 , tq1 = thinPullback t0 th t1 ph qt
      T , Tq0 , Tq1 = thinPullback T0 th T1 ph qT
  in  (t :: T) , reff _::_ =$= tq0 =$= Tq0 , reff _::_ =$= tq1 =$= Tq1
thinPullback (t0 :: t1) th (# x) ph ()
thinPullback (t0 :: t1) th (t2 / t3) ph ()
thinPullback (# x) th (t1 :: t2) ph ()
thinPullback (# x) th (# y) ph q with x - th | mkTri x th | y - ph | mkTri y ph
thinPullback (# x) th (# y) ph refl | x' | c | .x' | d with pullback th ph | isPullback c d
... | p , th' , ph' , ps , a , b | z , e , f , g
    = # z , #_ $= triDet (mkTri z th') e , #_ $= triDet (mkTri z ph') g
thinPullback (# x) th (t1 / t2) ph ()
thinPullback (t0 / t1) th (t2 :: t3) ph ()
thinPullback (t0 / t1) th (# x) ph ()
thinPullback (e0 / s0) th (e1 / s1) ph q = termNoConf _ _ q \ eq sq ->
  let e , eq0 , eq1 = thinPullback e0 th e1 ph eq
      s , sq0 , sq1 = thinPullback s0 th s1 ph sq
  in  (e / s) , reff _/_ =$= eq0 =$= sq0 , reff _/_ =$= eq1 =$= sq1

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
hole +T f = f
(s' <, t) +T f = (s' +T f) , t
(s ,> t') +T f = s , (t' +T f)
(! t') +T f = ! (t' +T f)
[ t' ] +T f = [ t' +T f ]
(t' <:: T) +T f = (t' +T f) :: T
(t ::> T') +T f = t :: (T' +T f)
(e' </ s) +T f = (e' +T f) / s
(e /> s') +T f = e / (s' +T f)

data DepCheck {n m : Nat}(th : n <= m){d : Dir} : Term m d -> Set where
  depGood : (t : Term n d) -> DepCheck th (t ^T th)
  depBad  : (x : 1 <= miss th){k : Nat}(t' : Term' m k d) ->
              DepCheck th (t' +T (# (x - (not th - oterm' t'))))

depBadIsNotGood : {n m : Nat}(th : n <= m){d : Dir}
  (x : 1 <= miss th){k : Nat}(t' : Term' m k d)
  (t : Term n d) -> (t ^T th) == (t' +T (# (x - (not th - oterm' t')))) -> Zero
depBadIsNotGood th x hole (t :: T) ()
depBadIsNotGood th x hole (# y) q with y - th | notLemma th y x
depBadIsNotGood th x hole (# y) refl | .(x - (not th - oi)) | b rewrite not th -oi = b refl
depBadIsNotGood th x hole (e / s) ()
depBadIsNotGood th x (t' <, x₁) ($ x₂) ()
depBadIsNotGood th x (s' <, t) (s0 , t0) q = termNoConf _ _ q \ q0 q1 -> depBadIsNotGood th x s' s0 q0
depBadIsNotGood th x (t' <, x₁) (! t) ()
depBadIsNotGood th x (t' <, x₁) [ t ] ()
depBadIsNotGood th x (x₁ ,> t') ($ x₂) ()
depBadIsNotGood th x (s ,> t') (s0 , t0) q = termNoConf _ _ q \ q0 q1 -> depBadIsNotGood th x t' t0 q1
depBadIsNotGood th x (x₁ ,> t') (! t) ()
depBadIsNotGood th x (x₁ ,> t') [ t ] ()
depBadIsNotGood th x (! t') ($ x₁) ()
depBadIsNotGood th x (! t') (t , t₁) ()
depBadIsNotGood th x (! t') (! t) q = termNoConf _ _ q help where
  help : (t ^T th os) == (t' +T (# (x - (not th - opred (oterm' t'))))) -> Zero
  help q0 with depBadIsNotGood (th os) x t' t
  ... | b rewrite opredLemma (not th) (oterm' t') = b q0
depBadIsNotGood th x (! t') [ t ] ()
depBadIsNotGood th x [ t' ] ($ x₁) ()
depBadIsNotGood th x [ t' ] (t , t₁) ()
depBadIsNotGood th x [ t' ] (! t) ()
depBadIsNotGood th x [ t' ] [ t ] q = termNoConf _ _ q (depBadIsNotGood th x t' t)
depBadIsNotGood th x (t' <:: T) (t :: _) q = termNoConf _ _ q \ q0 q1 -> depBadIsNotGood th x t' t q0
depBadIsNotGood th x (t' <:: x₁) (# x₂) ()
depBadIsNotGood th x (t' <:: x₁) (t / t₁) ()
depBadIsNotGood th x (x₁ ::> T') (t :: T) q = termNoConf _ _ q \ q0 q1 -> depBadIsNotGood th x T' T q1
depBadIsNotGood th x (x₁ ::> t') (# x₂) ()
depBadIsNotGood th x (x₁ ::> t') (t / t₁) ()
depBadIsNotGood th x (t' </ x₁) (t :: t₁) ()
depBadIsNotGood th x (t' </ x₁) (# x₂) ()
depBadIsNotGood th x (e' </ _) (e / _) q = termNoConf _ _ q \ q0 q1 -> depBadIsNotGood th x e' e q0
depBadIsNotGood th x (x₁ /> t') (t :: t₁) ()
depBadIsNotGood th x (x₁ /> t') (# x₂) ()
depBadIsNotGood th x (_ /> s') (_ / s) q = termNoConf _ _ q \ q0 q1 -> depBadIsNotGood th x s' s q1

depCheck : {n m : Nat}(th : n <= m){d : Dir}(t : Term m d) -> DepCheck th t
depCheck th ($ x) = depGood ($ x)
depCheck th (s , t) with depCheck th s | depCheck th t
depCheck th (.(s ^T th) , .(t ^T th)) | depGood s | depGood t = depGood (s , t)
depCheck th (s , .(t' +T (# (x - (not th - oterm' t'))))) | depGood _ | depBad x t'
  = depBad x (s ,> t')
depCheck th (.(s' +T (# (x - (not th - oterm' s')))) , t) | depBad x s' | _ = depBad x (s' <, t)
depCheck th (! t) with depCheck (th os) t
depCheck th (! .(t ^T th os)) | depGood t = depGood (! t)
depCheck th (! .(t' +T (# (x - (not th o' - oterm' t'))))) | depBad x t'
  rewrite opredLemma (not th) (oterm' t') = depBad x (! t')
depCheck th [ e ] with depCheck th e
depCheck th [ .(e ^T th) ] | depGood e = depGood [ e ]
depCheck th [ .(e' +T (# (x - (not th - oterm' e')))) ] | depBad x e' = depBad x [ e' ]
depCheck th (t :: T) with depCheck th t | depCheck th T
depCheck th (.(t ^T th) :: .(T ^T th)) | depGood t | depGood T = depGood (t :: T)
depCheck th (t :: .(T' +T (# (x - (not th - oterm' T'))))) | depGood _ | depBad x T' = depBad x (t ::> T')
depCheck th (.(t' +T (# (x - (not th - oterm' t')))) :: T) | depBad x t' | _ = depBad x (t' <:: T)
depCheck th (# x) with elem? th x
depCheck th (# .(x - th)) | yes x = depGood (# x)
depCheck th (# .(x - not th)) | no x with the (DepCheck th (# (x - (not th - oi)))) (depBad x hole)
... | a rewrite not th -oi = a
depCheck th (e / s) with depCheck th e | depCheck th s
depCheck th (.(e ^T th) / .(s ^T th)) | depGood e | depGood s = depGood (e / s)
depCheck th (e / .(s' +T (# (x - (not th - oterm' s'))))) | depGood _ | depBad x s' = depBad x (e /> s')
depCheck th (.(e' +T (# (x - (not th - oterm' e')))) / s) | depBad x e' | _ = depBad x (e' </ s)

depCheckLemma :  {n m : Nat}(th : n <= m){d : Dir}(t : Term n d) -> depCheck th (t ^T th) == depGood t
depCheckLemma th ($ x) = refl
depCheckLemma th (ta , td) rewrite depCheckLemma th ta | depCheckLemma th td = refl
depCheckLemma th (! t) rewrite depCheckLemma (th os) t = refl
depCheckLemma th [ e ] rewrite depCheckLemma th e = refl
depCheckLemma th (t :: T) rewrite depCheckLemma th t | depCheckLemma th T = refl
depCheckLemma th (# x) rewrite elemLemma th x = refl
depCheckLemma th (e / s) rewrite depCheckLemma th e | depCheckLemma th s = refl

Stan : {m : Nat} -> Pat m -> Nat -> Set
Stan ($ x) n = One
Stan (pa , pd) n = Stan pa n * Stan pd n
Stan (! p) n = Stan p n
Stan [? th ] n = Term (n +N domo th) chk
Stan >< n = Zero

stan : {m n : Nat}(p : Pat m)(ts : Stan p n) -> Term (n +N m) chk
stan ($ x) <> = $ x
stan (pa , pd) (tsa , tsd) = stan pa tsa , stan pd tsd
stan (! p) ts = ! stan p ts
stan [? th ] t = t ^T oi +th th
stan >< ()

data Match? {m n : Nat}(p : Pat m) : Term (n +N m) chk -> Set where
  yes : (ts : Stan p n) -> Match? p (stan p ts)
  no  : {t : Term (n +N m) chk} -> ((ts : Stan p n) -> stan p ts == t -> Zero) -> Match? p t

match? : {m n : Nat}(p : Pat m)(t : Term (n +N m) chk) -> Match? p t
match? ($ x) ($ y) with atomEq? x y
match? ($ x) ($ .x) | yes refl = yes <>
match? ($ x) ($ y) | no bad = no \ { u refl -> bad refl }
match? ($ x) (_ , _) = no \ ts ()
match? ($ x) (! t) = no \ ts ()
match? ($ x) [ t ] = no \ ts ()
match? (pa , pd) ($ x) = no \ ts ()
match? (pa , pd) (ta , td) with match? pa ta
match? (pa , pd) (.(stan pa tsa) , td) | yes tsa with match? pd td
match? (pa , pd) (.(stan pa tsa) , .(stan pd tsd)) | yes tsa | yes tsd = yes (tsa , tsd)
match? (pa , pd) (ta , td) | yes tsa | no bad = no help where
  help : (ts : Stan pa _ * Stan pd _) ->
         _==_ {Term _ _} (stan pa (fst ts) , stan pd (snd ts)) (stan pa tsa , td) -> Zero
  help (_ , tsd) q with stan pa tsa
  help (_ , tsd) refl | _ = bad tsd refl
match? (pa , pd) (ta , td) | no bad = no \ { ts refl -> bad _ refl } 
match? (pa , pd) (! t) = no \ ts ()
match? (pa , pd) [ t ] = no \ ts ()
match? (! p) ($ x) = no \ ts ()
match? (! p) (ta , td) = no \ ts ()
match? (! p) (! t) with match? p t
match? (! p) (! .(stan p ts)) | yes ts = yes ts
match? (! p) (! t) | no bad = no \ { ts refl -> bad _ refl }
match? (! p) [ t ] = no \ ts ()
match? [? th ] t with depCheck (oi +th th) t
match? [? th ] .(t ^T (oi +th th)) | depGood t = yes t
match? [? th ] .(t' +T (# (x - (not (oi +th th) - oterm' t')))) | depBad x t' = no (depBadIsNotGood (oi +th th) x t')
match? >< t = no \ ()

matchLemma : {n m : Nat}(p : Pat m)(ts : Stan p n) -> match? p (stan p ts) == yes ts
matchLemma ($ x) ts rewrite atomEqLemma x = refl
matchLemma (pa , pd) (tsa , tsd) rewrite matchLemma pa tsa | matchLemma pd tsd = refl
matchLemma (! p) ts rewrite matchLemma p ts = refl
matchLemma [? th ] t rewrite depCheckLemma (oi +th th) t = refl
matchLemma >< ()

_^P_ : forall {n m} -> Pat n -> n <= m -> Pat m
$ x ^P th = $ x
(pa , pd) ^P th = pa ^P th , pd ^P th
(! p) ^P th = ! p ^P (th os)
[? ph ] ^P th = [? ph - th ]
>< ^P th = ><

stanThin : forall {k n m}(p : Pat n)(th : n <= m) ->
   (ts' : Stan (p ^P th) k) -> Sg (Stan p k) \ ts -> stan (p ^P th) ts' == (stan p ts ^T (oi +th th))
stanThin ($ x) th <> = <> , refl
stanThin (pa , pd) th (tsa' , tsd') with stanThin pa th tsa' | stanThin pd th tsd'
... | tsa , qa | tsd , qd rewrite qa | qd = _ , refl
stanThin (! p) th ts' with stanThin p (th os) ts'
... | ts , q rewrite q = _ , refl
stanThin [? ph ] th t' = t' , (
  (t' ^T oi +th (ph - th))
    =< (t' ^T_) $= ((_+th (ph - th)) $= (oi -oi)) ]=
  (t' ^T ((oi - oi) +th (ph - th)))
    =[ (t' ^T_) $= [ oi - oi ]+th[ ph - th ] >=
  (t' ^T (oi +th ph - oi +th th))
    =[ t' ^T[ oi +th ph - oi +th th ] >=
  (t' ^T oi +th ph ^T oi +th th)
    [QED])
stanThin >< th ()

data Refine {m : Nat} : Pat m -> Pat m -> Set where
  $ : (x : Atom) -> Refine ($ x) ($ x)
  _,_ : forall {s0 s1 t0 t1} -> Refine s0 s1 -> Refine t0 t1 -> Refine (s0 , t0) (s1 , t1)
  !_  : forall {t0 t1} -> Refine t0 t1 -> Refine (! t0) (! t1)
  [?_] : forall {n}{th : n <= m}(p : Pat n) -> Refine [? th ] (p ^P th)
  >< : {p : Pat m} -> Refine p ><

refiner : forall {k m : Nat}{p p' : Pat m}(r : Refine p p')(ts' : Stan p' k) ->
               Sg (Stan p k) \ ts -> stan p' ts' == stan p ts
refiner ($ x) <> = <> , refl
refiner (ra , rd) (tsa' , tsd') with refiner ra tsa' | refiner rd tsd'
... | tsa , qa | tsd , qd rewrite qa | qd = (tsa , tsd) , refl
refiner (! r) ts' with refiner r ts'
... | ts , q rewrite q = ts , refl
refiner [? p ] ts' with stanThin p _ ts'
... | ts , q = stan p ts , q
refiner >< ()

restrict : {n m : Nat}(th : n <= m)(p : Pat m) -> Pat n
restrict th ($ x) = $ x
restrict th (pa , pd) = restrict th pa , restrict th pd
restrict th (! p) = ! restrict (th os) p
restrict th [? ph ] = let _ , th' , ph' , ps , _ , _ = pullback th ph in [? th' ]
restrict th >< = ><

restrictRefine : {n m : Nat}(th : n <= m)(p : Pat m) -> Refine p (restrict th p ^P th)
restrictRefine th ($ x) = $ x
restrictRefine th (pa , pd) = restrictRefine th pa , restrictRefine th pd
restrictRefine th (! p) = ! restrictRefine (th os) p
restrictRefine th [? ph ] with pullback th ph
... | _ , th' , ph' , ps , a , b with the (Refine [? ph ] [? ph' - ph ]) [? [? ph' ] ]
... | r rewrite triDet (mkTri ph' ph) b | triDet (mkTri th' th) a = r
restrictRefine th >< = ><

restrictStan : {k n m : Nat}(th : n <= m)(p : Pat m)(t : Term (k +N n) chk)
               (ts : Stan p k) -> (t ^T oi +th th) == stan p ts
               -> Stan (restrict th p ^P th) k
restrictStan th ($ x) t ts q = <>
restrictStan th (pa , pd) ($ x) ts ()
restrictStan th (pa , pd) (ta , td) (tsa , tsd) q = termNoConf _ _ q \ qa qd ->
  restrictStan th pa ta tsa qa , restrictStan th pd td tsd qd
restrictStan th (pa , pd) (! t) ts ()
restrictStan th (pa , pd) [ t ] ts ()
restrictStan th (! p) ($ x) ts ()
restrictStan th (! p) (_ , _) ts ()
restrictStan th (! p) (! t) ts q = termNoConf _ _ q \ q' -> restrictStan (th os) p t ts q'
restrictStan th (! p) [ t ] ts ()
restrictStan {k} th [? ph ] t0 t1 q with thinPullback t0 (oi +th th) t1 (oi +th ph) q
... | t , q0 , q1 with pullback th ph | pullback+Lemma (oi {k}) oi th ph
... | p , _ | qp rewrite pullbackoi {k} | qp = t
restrictStan th >< t () q

patU : {m : Nat}(p0 p1 : Pat m) ->
       Sg (Pat m) \ p -> Refine p0 p * Refine p1 p
patU ($ x) ($ y) with atomEq? x y
patU ($ x) ($ .x) | yes refl = $ x , $ x , $ x
patU ($ x) ($ y) | no b =  _ , >< , ><
patU ($ x) (p1 , p2) = _ , >< , ><
patU ($ x) (! p1) = _ , >< , ><
patU (p0 , p1) ($ x) = _ , >< , ><
patU (pa0 , pd0) (pa1 , pd1) =
  let _ , ra0 , ra1 = patU pa0 pa1
      _ , rd0 , rd1 = patU pd0 pd1
  in  _ , (ra0 , rd0) , (ra1 , rd1)
patU (p0 , p1) (! p2) = _ , >< , ><
patU (! p0) ($ x) = _ , >< , ><
patU (! p0) (p1 , p2) = _ , >< , ><
patU (! p0) (! p1) = let _ , r0 , r1 = patU p0 p1 in _ , (! r0) , (! r1)
patU [? th ] p1 = restrict th p1 ^P th , [? restrict th p1 ] , restrictRefine th p1
patU >< p1 = _ , >< , ><
patU p0 [? ph ] = restrict ph p0 ^P ph , restrictRefine ph p0 , [? restrict ph p0 ]
patU p0 >< = _ , >< , ><

mgU : {n m : Nat}(p0 p1 : Pat m)(ts0 : Stan p0 n)(ts1 : Stan p1 n) ->
      stan p0 ts0 == stan p1 ts1 ->
      Stan (fst (patU p0 p1)) n
mgU ($ x) ($ .x) ts0 ts1 refl rewrite atomEqLemma x = <>
mgU ($ x) (p1 , p2) ts0 ts1 ()
mgU ($ x) (! p1) ts0 ts1 ()
mgU p@($ x) [? th ] ts t q = restrictStan th p t ts (sym q)
mgU ($ x) >< ts0 () q
mgU (p0 , p1) ($ x) ts0 ts1 ()
mgU (pa0 , pd0) (pa1 , pd1) (tsa0 , tsd0) (tsa1 , tsd1) q = termNoConf _ _ q \ qa qd ->
  (mgU pa0 pa1 tsa0 tsa1 qa) , (mgU pd0 pd1 tsd0 tsd1 qd)
mgU (p0 , p1) (! p2) ts0 ts1 ()
mgU p@(p0 , p1) [? th ] ts t q = restrictStan th p t ts (sym q)
mgU (p0 , p1) >< ts0 () q
mgU (! p0) ($ x) ts0 ts1 ()
mgU (! p0) (p1 , p2) ts0 ts1 ()
mgU (! p0) (! p1) ts0 ts1 q = termNoConf _ _ q \ q' ->
  mgU p0 p1 ts0 ts1 q'
mgU p@(! p0) [? th ] ts t q = restrictStan th p t ts (sym q)
mgU (! p0) >< ts0 () q
mgU [? th ] p t ts1 q = restrictStan th p t ts1 q
mgU >< p () ts1 q
