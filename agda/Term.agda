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

data Term (hz : Bwd Nat)(m : Nat) : Dir -> Set where
  $    : Atom -> Term hz m chk
  _,_  : Term hz m chk -> Term hz m chk -> Term hz m chk
  !_   : Term hz (m su) chk -> Term hz m chk
  [_]  : Term hz m syn -> Term hz m chk
  _//_ : {h : Nat} -> El h hz -> BVec (Term hz m syn) h -> Term hz m chk
  _::_ : Term hz m chk -> Term hz m chk -> Term hz m syn
  #_   : 1 <= m -> Term hz m syn
  _/_  : Term hz m syn -> Term hz m chk -> Term hz m syn
infixr 4 _,_
infixr 3 !_
infixl 5 _/_ _::_
infix 6 #_


-- constructors are injective and disjoint -----------------------------------

-- if you know t0 == t1, how do you prove P?
termNoConfSubg : forall {hz m d}(t0 t1 : Term hz m d) -> Set -> Set
termNoConfSubg ($ x0)           ($ x1) P = x0 == x1 -> P
termNoConfSubg (s0 , t0)     (s1 , t1) P = s0 == s1 -> t0 == t1 -> P
termNoConfSubg (! t0)           (! t1) P = t0 == t1 -> P
termNoConfSubg [ e0 ]           [ e1 ] P = e0 == e1 -> P
termNoConfSubg (t0 :: T0)   (t1 :: T1) P = t0 == t1 -> T0 == T1 -> P
termNoConfSubg (# x0)           (# x1) P = x0 == x1 -> P
termNoConfSubg (e0 / s0)     (e1 / s1) P = e0 == e1 -> s0 == s1 -> P
termNoConfSubg (_//_ {j0} h0 ez0) (_//_ {j1} h1 ez1) P =
  Pi (j0 == j1) \ { refl -> h0 == h1 -> ez0 == ez1 -> P }
termNoConfSubg _                   _ _ = One

-- ain't no lie!
termNoConf : forall {hz m d}{t0 t1 : Term hz m d} -> t0 == t1 ->
  {P : Set} -> termNoConfSubg t0 t1 P -> P
termNoConf {t0 = $ x}      refl p = p refl
termNoConf {t0 = ta , td}  refl p = p refl refl
termNoConf {t0 = ! t}      refl p = p refl
termNoConf {t0 = [ e ]}    refl p = p refl
termNoConf {t0 = h // ez}  refl p = p refl refl refl
termNoConf {t0 = t0 :: t1} refl p = p refl refl
termNoConf {t0 = # i}      refl p = p refl
termNoConf {t0 = e / s}    refl p = p refl refl


-- object variable morphisms -------------------------------------------------

record Mor (M : Bwd Nat -> Nat -> Nat -> Set) : Set where
  field
    weak : forall {hz n m} -> M hz n m -> M hz (n su) (m su)
    hit  : forall {hz n m} -> (1 <= n) -> M hz n m -> Term hz m syn

module ACTION {M}(Kit : Mor M) where

  open Mor Kit

  act : forall {hz n m d} -> Term hz n d -> M hz n m -> Term hz m d
  actz : forall {hz n m h} ->
         BVec (Term hz n syn) h -> M hz n m -> BVec (Term hz m syn) h
  act ($ x)     m = $ x
  act (ta , td) m = act ta m , act td m
  act (! t)     m = ! act t (weak m)
  act [ e ]     m = [ act e m ]
  act (h // ez) m = h // actz ez m
  act (t :: T)  m = act t m :: act T m
  act (# i)     m = hit i m
  act (e / s)   m = act e m / act s m
  actz []       m = []
  actz (ez & e) m = actz ez m & act e m


-- thinning terms ------------------------------------------------------------

module _ where

  open Mor
  Thin : Mor \ hz -> _<=_
  weak Thin th = th os
  hit  Thin i th = # (i - th)

  _^T_ : forall {hz n m d} -> Term hz n d -> n <= m -> Term hz m d
  t ^T th = act t th where open ACTION Thin

  infixl 3 _^T_
  

-- identity morphisms --------------------------------------------------------

module IDENTITY {M}(Kit : Mor M) where

  open Mor Kit
  open ACTION Kit

  record IsIdentity {hz n}(f : M hz n n) : Set where
    coinductive
    field
      hitId  : (i : 1 <= n) -> hit i f == (# i)
      weakId : IsIdentity (weak f)

  open IsIdentity public

  actId : forall {hz n d}(t : Term hz n d)
          (f : M hz n n)(fId : IsIdentity f) ->
          act t f == t
  actzId : forall {hz n h}(ez : BVec (Term hz n syn) h)
           (f : M hz n n)(fId : IsIdentity f) ->
           actz ez f == ez
  actId ($ x)     f fId                                         = refl
  actId (ta , td) f fId rewrite actId ta f fId | actId td f fId = refl
  actId (! t)     f fId rewrite actId t (weak f) (weakId fId)   = refl
  actId [ e ]     f fId rewrite actId e f fId                   = refl
  actId (h // ez) f fId rewrite actzId ez f fId                 = refl
  actId (t :: T)  f fId rewrite actId t f fId | actId T f fId   = refl
  actId (# i)     f fId = hitId fId i
  actId (e / s)   f fId rewrite actId e f fId | actId s f fId   = refl
  actzId []       f fId                                         = refl
  actzId (ez & e) f fId rewrite actzId ez f fId | actId e f fId = refl
  
_^Toi : forall {hz n d} -> (t : Term hz n d) -> (t ^T oi) == t
t ^Toi = actId t oi oiId where
  open Mor Thin
  open IDENTITY Thin
  oiId : forall {hz n} -> IsIdentity {hz}{n} oi
  hitId  oiId i rewrite i -oi = refl
  weakId oiId = oiId


-- composite morphisms -------------------------------------------------------

module COMPOSITE {MF MB MC}(KitF : Mor MF)(KitB : Mor MB)(KitC : Mor MC) where

  open Mor
  open ACTION

  record IsComposite {hz p n m}
         (f : MF hz p n)(b : MB hz n m)(c : MC hz p m) : Set where
    coinductive
    field
      hitCo  : (i : 1 <= p) -> hit KitC i c == act KitB (hit KitF i f) b
      weakCo : IsComposite (weak KitF f) (weak KitB b) (weak KitC c)

  open IsComposite public

  actCo : forall {hz p n m d}(t : Term hz p d)
          (f : MF hz p n)(b : MB hz n m)(c : MC hz p m)
          (fbc : IsComposite f b c) ->
          act KitC t c == act KitB (act KitF t f) b
  actzCo : forall {hz p n m h}(ez : BVec (Term hz p syn) h)
           (f : MF hz p n)(b : MB hz n m)(c : MC hz p m)
           (fbc : IsComposite f b c) ->
           actz KitC ez c == actz KitB (actz KitF ez f) b
  actCo ($ x)     f b c fbc                         = refl
  actCo (ta , td) f b c fbc
    rewrite actCo ta f b c fbc | actCo td f b c fbc = refl
  actCo (! t)     f b c fbc
    rewrite actCo t (weak KitF f) (weak KitB b) (weak KitC c) (weakCo fbc) =
    refl
  actCo [ e ]     f b c fbc
    rewrite actCo e f b c fbc                       = refl
  actCo (h // ez) f b c fbc
    rewrite actzCo ez f b c fbc                     = refl
  actCo (t :: T)  f b c fbc
    rewrite actCo t f b c fbc | actCo T f b c fbc   = refl
  actCo (# i)     f b c fbc = hitCo fbc i
  actCo (e / s)   f b c fbc
    rewrite actCo e f b c fbc | actCo s f b c fbc   = refl
  actzCo []       f b c fbc                         = refl
  actzCo (ez & e) f b c fbc
    rewrite actzCo ez f b c fbc | actCo e f b c fbc = refl

_^T[_-_] : forall {hz p n m d} ->
           (t : Term hz p d)(th : p <= n)(ph : n <= m) ->
           (t ^T (th - ph)) == ((t ^T th) ^T ph)
t ^T[ th - ph ] = actCo t th ph (th - ph) (triCo (mkTri th ph)) where
  open Mor Thin
  open ACTION Thin
  open COMPOSITE Thin Thin Thin
  triCo : forall {hz p n m}{th : p <= n}{ph : n <= m}{ps : p <= m} ->
          Tri th ph ps -> IsComposite {hz} th ph ps
  hitCo (triCo {th = th} {ph} t) i
    rewrite triDet t (mkTri th ph) | i -[ th - ph ] = refl
  weakCo (triCo t) = triCo (t tsss)


-- a key fact about dependency -----------------------------------------------

-- if the same term is in the image of two thinnings,
-- then it is in the image of their pullback

thinPullback : {n0 n1 m : Nat}{d : Dir}
  (t0 : Term [] n0 d)(th : n0 <= m)(t1 : Term [] n1 d)(ph : n1 <= m) ->
  (t0 ^T th) == (t1 ^T ph) ->
  let p , th' , ph' , _ = pullback th ph
  in  Sg (Term [] p d) \ t -> ((t ^T th') == t0) * ((t ^T ph') == t1)

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

thinPullback (() // _) _ _ _ _
thinPullback _ _ (() // _) _ _


-- substitutions -------------------------------------------------------------

proj : {n : Nat}{X : Set} -> 1 <= n -> BVec X n -> X
proj (i o') (xz & x) = proj i xz
proj (i os) (xz & x) = x

projPure : {n : Nat}{X : Set}(i : 1 <= n)(x : X) -> proj i (pure x) == x
projPure (i o') x = projPure i x
projPure (i os) x = refl

projApp : {n : Nat}{S T : Set}
          (i : 1 <= n)(fz : BVec (S -> T) n)(sz : BVec S n) ->
          proj i (fz <*> sz) == proj i fz (proj i sz)
projApp (i o') (fz & f) (sz & s) = projApp i fz sz
projApp (i os) (fz & f) (sz & s) = refl

projSelect : forall {n m X}(i : 1 <= n)(th : n <= m)(xz : BVec X m) ->
  proj i (select th xz) == proj (i - th) xz
projSelect i (th o') (xz & x) = projSelect i th xz
projSelect (i o') (th os) (xz & x) = projSelect i th xz
projSelect (i os) (th os) (xz & x) = refl
projSelect () oz []

SUBST : Bwd Nat -> Nat -> Nat -> Set
SUBST hz n m = BVec (Term hz m syn) n

module _ where

  open Mor

  Subst : Mor SUBST
  weak Subst ez = (pure (_^T (oi o')) <*> ez) & # (oe os) 
  hit  Subst = proj

  _$T_ : forall {hz n m d}(t : Term hz n d)(ez : SUBST hz n m) -> Term hz m d
  t $T ez = act t ez where
    open ACTION Subst

  idSubst : forall {hz n} -> SUBST hz n n
  idSubst {n = ze} = []
  idSubst {n = n su} = weak Subst idSubst

  open IDENTITY Subst

  idSubstLemma : forall {hz n} -> (i : 1 <= n) -> proj i (idSubst {hz}) == (# i)
  idSubstLemma (i o') =
    proj i (pure (_^T (oi o')) <*> idSubst)
      =[ projApp i _ _ >=
    proj i (pure (_^T (oi o'))) (proj i idSubst)
      =[ projPure i _ =$= idSubstLemma i >=
    (# ((i - oi) o'))
      =[ #_ $= (_o' $= (i -oi)) >=
    (# i o')
      [QED]
  idSubstLemma (i os) = #_ $= (_os $= oe! oe i)
  idSubstId : forall {hz n} -> IsIdentity {hz}{n} idSubst
  hitId  idSubstId = idSubstLemma
  weakId idSubstId = idSubstId

module _ where

  open Mor
  open COMPOSITE Thin Subst Subst

  thinSubstSubstCo : forall {hz p n m}(th : p <= n)(ez : SUBST hz n m)
                     (fz : SUBST hz p m) -> select th ez == fz ->
                     IsComposite th ez fz
  hitCo  (thinSubstSubstCo th ez ._ refl) i = projSelect i th ez
  weakCo (thinSubstSubstCo th ez fz q) =
    thinSubstSubstCo (th os) ((pure (_^T (oi o')) <*> ez) & # oe os)
      ((pure (_^T (oi o')) <*> fz) & # oe os)
      ((_& _) $=
        (select th (pure (_^T (oi o')) <*> ez)
           =[ selectApp th _ _ >=
         (select th (pure (_^T (oi o'))) <*> select th ez)
           =[ reff _<*>_ =$= selectPure th _ =$= q >=
         (pure (_^T (oi o')) <*> fz)
           [QED]))

  _^$T[_-_] : forall {hz p n m d}(t : Term hz p d)(th : p <= n)(ez : SUBST hz n m) ->
    ((t ^T th) $T ez) == (t $T select th ez)
  t ^$T[ th - ez ] = sym (actCo t th ez _ (thinSubstSubstCo _ _ _ refl)) 
  

module _ where

  open Mor
  open COMPOSITE Subst Thin Subst

  substThinSubstCo : forall {hz p n m}(ez : SUBST hz p n)(th : n <= m)
                     (fz : SUBST hz p m) -> (pure (_^T th) <*> ez) == fz ->
                     IsComposite ez th fz
  hitCo (substThinSubstCo ez th ._ refl) i =
    proj i (pure (_^T th) <*> ez)
      =[ projApp i _ _ >=
    proj i (pure (_^T th)) (proj i ez)
      =[ projPure i _ =$ proj i ez >=
    (proj i ez ^T th)
      [QED]
  weakCo (substThinSubstCo ez th fz q) = substThinSubstCo
    ((pure (_^T (oi o')) <*> ez) & # oe os)
    (th os)
    ((pure (_^T (oi o')) <*> fz) & # oe os)
    (reff _&_
     =$= ( (pure (_^T (th os)) <*> (pure (_^T (oi o')) <*> ez))
             =[ bVecMapMap (_^T (th os)) (_^T (oi o')) ez >=
           (pure ((_^T (th os)) ` (_^T (oi o'))) <*> ez)
             =[ bVecMapExt ((_^T (th os)) ` (_^T (oi o'))) ((_^T (oi o')) ` (_^T th))
                 (\ e -> ((e ^T (oi o')) ^T (th os))
                           =< e ^T[ oi o' - th os ] ]=
                         (e ^T ((oi - th) o'))
                           =[ (\ z -> e ^T (z o')) $= (oi- th) >=
                         (e ^T (th o'))
                           =< (\ z -> e ^T (z o')) $= (th -oi) ]=
                         (e ^T ((th - oi) o'))
                           =[ e ^T[ th - oi o' ] >=
                         ((e ^T th) ^T (oi o'))
                           [QED])
                ez >=
           (pure ((_^T (oi o')) ` (_^T th)) <*> ez)
             =< bVecMapMap  (_^T (oi o')) (_^T th) ez ]=
           (pure (_^T (oi o')) <*> (pure (_^T th) <*> ez))
             =[ (pure (_^T (oi o')) <*>_) $= q >=
           (pure (_^T (oi o')) <*> fz)
             [QED]
         )
     =$= (#_ $= (_os $= oe! _ _)))

  _$^T[_-_] : forall {hz p n m d}(t : Term hz p d)(ez : SUBST hz p n)(th : n <= m) ->
    ((t $T ez) ^T th) == (t $T (pure (_^T th) <*> ez))
  t $^T[ th - ez ] = sym (actCo t th ez _ (substThinSubstCo _ _ _ refl)) 

module _ where

  open Mor Subst
  open COMPOSITE Subst Subst Subst

  substSubstSubstCo : forall {hz p n m}(ez : SUBST hz p n)(fz : SUBST hz n m)
                     (gz : SUBST hz p m) -> (pure (_$T fz) <*> ez) == gz ->
                     IsComposite ez fz gz
  hitCo (substSubstSubstCo ez fz ._ refl) i =
    proj i (pure (_$T fz) <*> ez)
      =[ projApp i _ _ >=
    proj i (pure (_$T fz)) (proj i ez)
      =[ projPure i (_$T fz) =$ proj i ez >=
    (proj i ez $T fz)
      [QED]
  weakCo (substSubstSubstCo ez fz gz q) = substSubstSubstCo (weak ez) (weak fz) (weak gz)
    ((_& _) $= (
      (pure (_$T weak fz) <*> (pure (_^T (oi o')) <*> ez))
         =[ bVecMapMap (_$T weak fz) (_^T (oi o')) ez >=
      (pure ((_$T Subst .Mor.weak fz) ` (_^T (oi o'))) <*> ez)
         =[ bVecMapExt ((_$T Subst .Mor.weak fz) ` (_^T (oi o'))) ((_^T (oi o')) ` (_$T fz))
            (\ t -> ((t ^T (oi o')) $T weak fz)
                      =[ t ^$T[ oi o' - weak fz ] >=
                    (t $T (select oi (pure (_^T (oi o')) <*> fz)))
                      =[ (t $T_) $= selectoi _ >=
                    (t $T (pure (_^T (oi o')) <*> fz))
                      =< t $^T[ fz - oi o' ] ]=
                    ((t $T fz) ^T (oi o'))
                      [QED])
            ez >=
      (pure ((_^T (oi o')) ` (_$T fz)) <*> ez)
         =< bVecMapMap (_^T (oi o')) (_$T fz) ez ]=
      (pure (_^T (oi o')) <*> (pure (_$T fz) <*> ez))
         =[ (pure (_^T (oi o')) <*>_) $= q >=
      (pure (_^T (oi o')) <*> gz)
         [QED] ))

  _$T[_-_] : forall {hz p n m d}(t : Term hz p d)(ez : SUBST hz p n)(fz : SUBST hz n m) ->
    ((t $T ez) $T fz) == (t $T (pure (_$T fz) <*> ez))
  t $T[ ez - fz ] = sym (actCo t ez fz _ (substSubstSubstCo _ _ _ refl)) 

Env : Bwd Nat -> Nat -> Set
Env hz m = BAll (\ h -> Term [] (m +N h) chk) hz

_/T_ : forall {hz m d} -> Term hz m d -> Env hz m -> Term [] m d
_/Tz_ : forall {hz m h} -> BVec (Term hz m syn) h -> Env hz m -> BVec (Term [] m syn) h
$ x       /T tz = $ x
(ta , td) /T tz = (ta /T tz) , (td /T tz)
(! t)     /T tz = ! (t /T bAll (\ {h} -> (_^T ((oi o') +th (oi {h})))) tz)
[ e ]     /T tz = [ e /T tz ]
(h // ez) /T tz = aproj h tz $T (idSubst +V (ez /Tz tz))
(t :: T)  /T tz = (t /T tz) :: (T /T tz)
(# i)     /T tz = # i
(e / s)   /T tz = (e /T tz) / (s /T tz)
[] /Tz tz = []
(ez & e) /Tz tz = (ez /Tz tz) & (e /T tz)
