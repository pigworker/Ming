module Term where

open import Basics
open import Thinning


-- Atoms ---------------------------------------------------------------------

data Atom : Set where
  nil : Atom
  -- more to follow

atomEq? : (x y : Atom) -> Dec (x == y)
atomEq? nil nil = yes refl

atomEqLemma : (x : Atom) -> atomEq? x x == yes refl
atomEqLemma nil = refl


-- Terms ---------------------------------------------------------------------

data Dir : Set where chk syn : Dir

data Term (m : Nat) : Dir -> Set where
  $    : Atom -> Term m chk
  _,_  : Term m chk -> Term m chk -> Term m chk
  !_   : Term (m su) chk -> Term m chk
  [_]  : Term m syn -> Term m chk
  _::_ : Term m chk -> Term m chk -> Term m syn
  #_   : 1 <= m -> Term m syn
  _/_  : Term m syn -> Term m chk -> Term m syn
infixr 4 _,_
infixr 3 !_
infixl 5 _/_ _::_
infix 6 #_

-- constructors are injective and disjoint -----------------------------------

-- if you know t0 == t1, how do you prove P?
termNoConfSubg : forall {m d}(t0 t1 : Term m d) -> Set -> Set
termNoConfSubg ($ x0)         ($ x1) P = x0 == x1 -> P
termNoConfSubg ($ x)         (_ , _) P = One
termNoConfSubg ($ x)           (! _) P = One
termNoConfSubg ($ x)           [ _ ] P = One
termNoConfSubg (t0 , t1)       ($ x) P = One
termNoConfSubg (s0 , t0)   (s1 , t1) P = s0 == s1 -> t0 == t1 -> P
termNoConfSubg (t0 , t1)      (! t2) P = One
termNoConfSubg (t0 , t1)      [ t2 ] P = One
termNoConfSubg (! t0)          ($ x) P = One
termNoConfSubg (! t0)      (t1 , t2) P = One
termNoConfSubg (! t0)         (! t1) P = t0 == t1 -> P
termNoConfSubg (! t0)         [ t1 ] P = One
termNoConfSubg [ t0 ]          ($ x) P = One
termNoConfSubg [ t0 ]      (t1 , t2) P = One
termNoConfSubg [ t0 ]         (! t1) P = One
termNoConfSubg [ e0 ]         [ e1 ] P = e0 == e1 -> P
termNoConfSubg (t0 :: T0) (t1 :: T1) P = t0 == t1 -> T0 == T1 -> P
termNoConfSubg (t0 :: t1)      (# x) P = One
termNoConfSubg (t0 :: t1)  (t2 / t3) P = One
termNoConfSubg (# x)      (t1 :: t2) P = One
termNoConfSubg (# x0)         (# x1) P = x0 == x1 -> P
termNoConfSubg (# x)       (t1 / t2) P = One
termNoConfSubg (t0 / t1)  (t2 :: t3) P = One
termNoConfSubg (t0 / t1)       (# x) P = One
termNoConfSubg (e0 / s0)   (e1 / s1) P = e0 == e1 -> s0 == s1 -> P

-- ain't no lie!
termNoConf : forall {m d}{t0 t1 : Term m d} -> t0 == t1 ->
  {P : Set} -> termNoConfSubg t0 t1 P -> P
termNoConf {t0 = $ x}      refl p = p refl
termNoConf {t0 = t0 , t1}  refl p = p refl refl
termNoConf {t0 = ! t0}     refl p = p refl
termNoConf {t0 = [ t0 ]}   refl p = p refl
termNoConf {t0 = t0 :: t1} refl p = p refl refl
termNoConf {t0 = # x}      refl p = p refl
termNoConf {t0 = t0 / t1}  refl p = p refl refl


-- thinning terms ------------------------------------------------------------

_^T_ : {n m : Nat}{d : Dir} -> Term n d -> n <= m -> Term m d
$ x      ^T th = $ x
(s , t)  ^T th = s ^T th , t ^T th 
(! t)    ^T th = ! t ^T th os
[ e ]    ^T th = [ e ^T th ]
(t :: T) ^T th = t ^T th :: T ^T th
(# x)    ^T th = # (x - th)
(e / s)  ^T th = e ^T th / s ^T th
infixl 6 _^T_

-- boring functoriality
_^Toi : {n : Nat}{d : Dir}(t : Term n d) -> (t ^T oi) == t
$ x      ^Toi                         = refl
(s , t)  ^Toi rewrite s ^Toi | t ^Toi = refl
(! t)    ^Toi rewrite t ^Toi          = refl
[ e ]    ^Toi rewrite e ^Toi          = refl
(t :: T) ^Toi rewrite t ^Toi | T ^Toi = refl
(# x)    ^Toi rewrite x -oi           = refl
(e / s)  ^Toi rewrite e ^Toi | s ^Toi = refl

_^T[_-_] : {p n m : Nat}{d : Dir}(t : Term p d)(th : p <= n)(ph : n <= m) ->
  (t ^T (th - ph)) == ((t ^T th) ^T ph)
$ x      ^T[ th - ph ]                                           = refl
(s , t)  ^T[ th - ph ] rewrite s ^T[ th - ph ] | t ^T[ th - ph ] = refl
(! t)    ^T[ th - ph ] rewrite t ^T[ th os - ph os ]             = refl
[ e ]    ^T[ th - ph ] rewrite e ^T[ th - ph ]                   = refl
(t :: T) ^T[ th - ph ] rewrite t ^T[ th - ph ] | T ^T[ th - ph ] = refl
(# x)    ^T[ th - ph ] rewrite x -[ th - ph ]                    = refl
(e / s)  ^T[ th - ph ] rewrite e ^T[ th - ph ] | s ^T[ th - ph ] = refl


-- a key fact about dependency -----------------------------------------------

-- if the same term is in the image of two thinnings,
-- then it is in the image of their pullback

thinPullback : {n0 n1 m : Nat}{d : Dir}
  (t0 : Term n0 d)(th : n0 <= m)(t1 : Term n1 d)(ph : n1 <= m) ->
  (t0 ^T th) == (t1 ^T ph) ->
  let p , th' , ph' , _ = pullback th ph
  in  Sg (Term p d) \ t -> ((t ^T th') == t0) * ((t ^T ph') == t1)

-- the variable case requires the universal property of the pullback
-- i.e., we didn't chuck away more variables than we had to
thinPullback (# x) th (# y) ph q with x - th | mkTri x th | y - ph | mkTri y ph
thinPullback (# x) th (# y) ph refl | x' | c | .x' | d
  with pullback th ph | isPullback c d
... | p , th' , ph' , ps , a , b | z , e , f , g
    = # z , #_ $= triDet (mkTri z th') e , #_ $= triDet (mkTri z ph') g

-- the matching structural cases make use of injectivity
thinPullback ($ x) th ($ .x) ph refl = $ x , refl , refl
thinPullback (ta0 , td0) th (ta1 , td1) ph q = termNoConf q \ qa qd ->
  let ta , aq0 , aq1 = thinPullback ta0 th ta1 ph qa
      td , dq0 , dq1 = thinPullback td0 th td1 ph qd
  in  (ta , td) , reff _,_ =$= aq0 =$= dq0 , reff _,_ =$= aq1 =$= dq1
thinPullback (! t0) th (! t1) ph q = termNoConf q \ q' -> 
  let t , q0 , q1 = thinPullback t0 (th os) t1 (ph os) q'
  in (! t) , !_ $= q0 , !_ $= q1 
thinPullback [ e0 ] th [ e1 ] ph q = termNoConf q \ eq ->
  let e , eq0 , eq1 = thinPullback e0 th e1 ph eq
  in [ e ] , [_] $= eq0 , [_] $= eq1
thinPullback (t0 :: T0) th (t1 :: T1) ph q = termNoConf q \ qt qT ->
  let t , tq0 , tq1 = thinPullback t0 th t1 ph qt
      T , Tq0 , Tq1 = thinPullback T0 th T1 ph qT
  in  (t :: T) , reff _::_ =$= tq0 =$= Tq0 , reff _::_ =$= tq1 =$= Tq1
thinPullback (e0 / s0) th (e1 / s1) ph q = termNoConf q \ eq sq ->
  let e , eq0 , eq1 = thinPullback e0 th e1 ph eq
      s , sq0 , sq1 = thinPullback s0 th s1 ph sq
  in  (e / s) , reff _/_ =$= eq0 =$= sq0 , reff _/_ =$= eq1 =$= sq1

-- the mismatching cases are obviously impossible
thinPullback ($ x) th (t1 , t2) ph ()
thinPullback ($ x) th (! t1) ph ()
thinPullback ($ x) th [ t1 ] ph ()
thinPullback (t0 , t1) th ($ x) ph ()
thinPullback (t0 , t1) th (! t2) ph ()
thinPullback (t0 , t1) th [ t2 ] ph ()
thinPullback (! t0) th ($ x) ph ()
thinPullback (! t0) th (t1 , t2) ph ()
thinPullback (! t0) th [ t1 ] ph ()
thinPullback [ t0 ] th ($ x) ph ()
thinPullback [ t0 ] th (t1 , t2) ph ()
thinPullback [ t0 ] th (! t1) ph ()
thinPullback (t0 :: t1) th (# x) ph ()
thinPullback (t0 :: t1) th (t2 / t3) ph ()
thinPullback (# x) th (t1 :: t2) ph ()
thinPullback (# x) th (t1 / t2) ph ()
thinPullback (t0 / t1) th (t2 :: t3) ph ()
thinPullback (t0 / t1) th (# x) ph ()
