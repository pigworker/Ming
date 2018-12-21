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

record Mor (M : Nat -> Nat -> Set) : Set where
  field
    weak : forall {n m} -> M n m -> M (n su) (m su)
    hit  : forall {hz n m} -> (1 <= n) -> M n m -> Term hz m syn

  weaks : forall {n m} -> M n m -> (k : Nat) -> M (n +N k) (m +N k)
  weaks f ze = f
  weaks f (k su) = weak (weaks f k)

module ACTION {M}(Kit : Mor M) where

  open Mor Kit

  act : forall {hz n m d} -> Term hz n d -> M n m -> Term hz m d
  actz : forall {hz n m h} ->
         BVec (Term hz n syn) h -> M n m -> BVec (Term hz m syn) h
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
  Thin : Mor _<=_
  weak Thin th = th os
  hit  Thin i th = # (i - th)

  _^T_ : forall {hz n m d} -> Term hz n d -> n <= m -> Term hz m d
  t ^T th = act t th where open ACTION Thin

  infixl 3 _^T_
  

-- identity morphisms --------------------------------------------------------

module IDENTITY {M}(Kit : Mor M) where

  open Mor Kit
  open ACTION Kit

  record IsIdentity {n}(f : M n n) : Set where
    coinductive
    field
      hitId  : forall {hz}(i : 1 <= n) -> hit {hz} i f == (# i)
      weakId : IsIdentity (weak f)

  open IsIdentity public

  actId : forall {hz n d}(t : Term hz n d)
          (f : M n n)(fId : IsIdentity f) ->
          act t f == t
  actzId : forall {hz n h}(ez : BVec (Term hz n syn) h)
           (f : M n n)(fId : IsIdentity f) ->
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
  oiId : forall {n} -> IsIdentity {n} oi
  hitId  oiId i rewrite i -oi = refl
  weakId oiId = oiId


-- composite morphisms -------------------------------------------------------

module COMPOSITE {MF MB MC}(KitF : Mor MF)(KitB : Mor MB)(KitC : Mor MC) where

  open Mor
  open ACTION

  record IsComposite {p n m}
         (f : MF p n)(b : MB n m)(c : MC p m) : Set where
    coinductive
    field
      hitCo  : forall {hz}(i : 1 <= p) ->
               hit KitC {hz} i c == act KitB (hit KitF i f) b
      weakCo : IsComposite (weak KitF f) (weak KitB b) (weak KitC c)

  open IsComposite public

  actCo : forall {hz p n m d}(t : Term hz p d)
          (f : MF p n)(b : MB n m)(c : MC p m)
          (fbc : IsComposite f b c) ->
          act KitC t c == act KitB (act KitF t f) b
  actzCo : forall {hz p n m h}(ez : BVec (Term hz p syn) h)
           (f : MF p n)(b : MB n m)(c : MC p m)
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
  triCo : forall {p n m}{th : p <= n}{ph : n <= m}{ps : p <= m} ->
          Tri th ph ps -> IsComposite th ph ps
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


-- metavariable actions ------------------------------------------------------

module _ where

  open ACTION

  record MetaMor (F : Bwd Nat -> Bwd Nat -> Nat -> Set) : Set1 where
    field
      splat : forall {hz kz h n} -> F hz kz n ->
              (x : El h hz) -> BVec (Term kz n syn) h -> Term kz n chk
      mmor : forall {M}(K : Mor M){hz kz n m} ->
              F hz kz n -> M n m -> F hz kz m

module META-ACTION {F}(Kit : MetaMor F) where

  open MetaMor Kit
  open ACTION

  mact : forall {hz kz n d}
         (t : Term hz n d)(f : F hz kz n) -> Term kz n d
  mactz : forall {hz kz n h}
          (tz : BVec (Term hz n syn) h)(f : F hz kz n) ->
          BVec (Term kz n syn) h
  mact ($ x)     f = $ x
  mact (ta , td) f = mact ta f , mact td f
  mact (! t)     f = ! mact t (mmor Thin f (oi o'))
  mact [ e ]     f = [ mact e f ]
  mact (x // ez) f = splat f x (mactz ez f)
  mact (t :: T)  f = mact t f :: mact T f
  mact (# i)     f = # i
  mact (e / s)   f = mact e f / mact s f
  mactz []       f = []
  mactz (ez & e) f = mactz ez f & mact e f


{-
    mthinId : forall {hz kz n}(f : F hz kz n) ->
       mthin f oi == f
    mthinCo : forall {hz kz p n m}(f : F hz kz p)
       {th : p <= n}{ph : n <= m}{ps : p <= m}(t : Tri th ph ps) ->
       mthin (mthin f th) ph == mthin f ps
-}
  module META-COMMUTE  {M}(K : Mor M)
    (splatcommu : forall {hz kz h n m} ->
                  (f : F hz kz n)(th : M n m)
                  (x : El h hz)(ez : BVec (Term kz n syn) h) ->
                  splat (mmor K f th) x (pure (\ e -> act K e th) <*> ez) ==
                    (act K (splat f x ez) th))
    (hitcommu : forall {hz kz n m}(i : 1 <= n)(th : M n m)(f : F hz kz n) ->
                 mact (Mor.hit K i th) (mmor K f th) == Mor.hit K i th)
    (weakcommu : forall {hz kz n m}(th : M n m)(f : F hz kz n) ->
                    mmor Thin (mmor K f th) (oi o') ==
                    mmor K (mmor Thin f (oi o')) (Mor.weak K th))

    where

    open Mor K

    mcommu : forall {hz kz n m d}
             (t : Term hz n d)(f : F hz kz n)
             (th : M n m) ->
             mact (act K t th) (mmor K f th) == (act K (mact t f) th)
    mcommuz : forall {hz kz n m h}
              (ez : BVec (Term hz n syn) h)(f : F hz kz n)
              (th : M n m) ->
              mactz (actz K ez th) (mmor K f th)
                == (pure (\ e -> act K e th) <*> mactz ez f)
    mcommuz [] f th = refl
    mcommuz (ez & e) f th = reff _&_ =$= mcommuz ez f th =$= mcommu e f th
    mcommu ($ x) f th = refl
    mcommu (ta , td) f th = reff _,_ =$= mcommu ta f th =$= mcommu td f th
    mcommu [ e ] f th = [_] $= mcommu e f th
    mcommu (t :: T) f th = reff _::_ =$= mcommu t f th =$= mcommu T f th
    mcommu (e / s) f th = reff _/_ =$= mcommu e f th =$= mcommu s f th
    mcommu (x // ez) f th =
      splat (mmor K f th) x (mactz (actz K ez th) (mmor K f th))
        =[ splat (mmor K f th) x $= mcommuz ez f th >=
      splat (mmor K f th) x (pure (\ e -> act K e th) <*> mactz ez f)
        =[ splatcommu f th x (mactz ez f) >=
      (act K (splat f x (mactz ez f)) th)
        [QED]
    mcommu (# i) f th = hitcommu i th f
    mcommu (! t) f th = !_ $= (
      mact (act K t (weak th)) (mmor Thin (mmor K f th) (oi o'))
        =[ mact (act K t (weak th)) $= weakcommu th f >=
      mact (act K t (weak th)) (mmor K (mmor Thin f (oi o')) (weak th))
        =[ mcommu t (mmor Thin f (oi o')) (weak th) >=
      act K (mact t (mmor Thin f (oi o'))) (weak th)
        [QED])


-- inflation -----------------------------------------------------------------

module _ where

  open MetaMor
  
  inflation : MetaMor \ hz _ _ -> hz == []
  splat inflation refl ()
  mmor inflation _ q _ = q

  open META-ACTION inflation

  inflate : forall {hz n d} -> Term [] n d -> Term hz n d
  inflate t = mact t refl

  open META-COMMUTE Thin
    (\ { refl _ () })
    (\ { t th refl -> refl })
    (\ _ _ -> refl)

  inflateThin : forall {hz n m d}(t : Term [] n d)(th : n <= m) ->
    inflate {hz} (t ^T th) == (inflate t ^T th)
  inflateThin t = mcommu t refl

inflated : forall {F}(K : MetaMor F)
             {hz kz n d}(t : Term [] n d)(f : F hz kz n) ->
             META-ACTION.mact K (inflate t) f == inflate t
inflated K ($ x) f = refl
inflated K (ta , td) f = reff _,_ =$= inflated K ta f =$= inflated K td f
inflated K (! t) f = !_ $= inflated K t (MetaMor.mmor K Thin f (oi o'))
inflated K [ e ] f = [_] $= inflated K e f
inflated K (() // _) f
inflated K (t :: T) f = reff _::_ =$= inflated K t f =$= inflated K T f
inflated K (# i) f = refl
inflated K (e / s) f = reff _/_ =$= inflated K e f =$= inflated K s f



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

SUBST : Nat -> Nat -> Set
SUBST n m = BVec (Term [] m syn) n

module _ where

  open Mor

  Subst : Mor SUBST
  weak Subst ez = (pure (_^T (oi o')) <*> ez) & # (oe os) 
  hit  Subst i ez = inflate (proj i ez)

  _$T_ : forall {hz n m d}(t : Term hz n d)(ez : SUBST n m) -> Term hz m d
  t $T ez = act t ez where
    open ACTION Subst

  idSubst : forall {n} -> SUBST n n
  idSubst {n = ze} = []
  idSubst {n = n su} = weak Subst idSubst

  open IDENTITY Subst

  idSubstLemma : forall {n} -> (i : 1 <= n) -> proj i idSubst == (# i)
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
  idSubstId : forall {n} -> IsIdentity {n} idSubst
  hitId  idSubstId i rewrite idSubstLemma i = refl
  weakId idSubstId = idSubstId

module _ where

  open META-ACTION inflation
  open META-COMMUTE Subst
    (\ { refl _ () })
    (\ { i ez refl -> inflated inflation (proj i ez) refl })
    (\ _ _ -> refl)

  inflateSubst : forall {hz n m d}(t : Term [] n d)(sg : SUBST n m) ->
    inflate {hz} (t $T sg) == (inflate t $T sg)
  inflateSubst t sg = mcommu t refl sg

module _ where

  open Mor
  open COMPOSITE Thin Subst Subst

  thinSubstSubstCo : forall {p n m}(th : p <= n)(ez : SUBST n m)
                     (fz : SUBST p m) -> select th ez == fz ->
                     IsComposite th ez fz
  hitCo  (thinSubstSubstCo th ez ._ refl) i =
    inflate (proj i (select th ez))
      =[ inflate $= projSelect i th ez >=
    inflate (proj (i - th) ez) [QED]
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

  _^$T[_-_] : forall {hz p n m d}(t : Term hz p d)(th : p <= n)(ez : SUBST n m) ->
    ((t ^T th) $T ez) == (t $T select th ez)
  t ^$T[ th - ez ] = sym (actCo t th ez _ (thinSubstSubstCo _ _ _ refl)) 
  
module _ where

  open Mor
  open COMPOSITE Subst Thin Subst

  substThinSubstCo : forall {p n m}(ez : SUBST p n)(th : n <= m)
                     (fz : SUBST p m) -> (pure (_^T th) <*> ez) == fz ->
                     IsComposite ez th fz
  hitCo (substThinSubstCo ez th ._ refl) i =
    inflate (proj i (pure (_^T th) <*> ez))
      =[ inflate $= (
        proj i (pure (_^T th) <*> ez)
          =[ projApp i _ _ >=
        proj i (pure (_^T th)) (proj i ez)
          =[ projPure i _ =$ proj i ez >=
        (proj i ez ^T th)
          [QED]
      ) >=
    inflate (proj i ez ^T th)
      =[ inflateThin (proj i ez) th >=
    (inflate (proj i ez) ^T th)
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

  _$^T[_-_] : forall {hz p n m d}(t : Term hz p d)(ez : SUBST p n)(th : n <= m) ->
    ((t $T ez) ^T th) == (t $T (pure (_^T th) <*> ez))
  t $^T[ th - ez ] = sym (actCo t th ez _ (substThinSubstCo _ _ _ refl)) 


module _ where

  open Mor Subst
  open COMPOSITE Subst Subst Subst

  substSubstSubstCo : forall {p n m}(ez : SUBST p n)(fz : SUBST n m)
                     (gz : SUBST p m) -> (pure (_$T fz) <*> ez) == gz ->
                     IsComposite ez fz gz
  hitCo (substSubstSubstCo ez fz ._ refl) i =
    inflate (proj i (pure (_$T fz) <*> ez))
      =[ inflate $= (
        proj i (pure (_$T fz) <*> ez)
          =[ projApp i _ _ >=
        proj i (pure (_$T fz)) (proj i ez)
          =[ projPure i (_$T fz) =$ proj i ez >=
        (proj i ez $T fz)
         [QED]) >=
    inflate (proj i ez $T fz)
      =[ inflateSubst (proj i ez) fz >=
    (inflate (proj i ez) $T fz)
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

  _$T[_-_] : forall {hz p n m d}(t : Term hz p d)(ez : SUBST p n)(fz : SUBST n m) ->
    ((t $T ez) $T fz) == (t $T (pure (_$T fz) <*> ez))
  t $T[ ez - fz ] = sym (actCo t ez fz _ (substSubstSubstCo _ _ _ refl)) 

Env : Bwd Nat -> Bwd Nat -> Nat -> Set
Env hz kz m = (kz == []) * BAll (\ h -> Term [] (m +N h) chk) hz

module _ where

  open Mor Thin

  selectWeaks : forall {n m}(th : n <= m) k {X} (xz : BVec X m)(yz : BVec X k) ->
    select (weaks th k) (xz +V yz) == (select th xz +V yz)
  selectWeaks th ze     xz []       = refl
  selectWeaks th (k su) xz (yz & y) = (_& y) $= selectWeaks th k xz yz 

module _ where

  open MetaMor
  open Mor
  open ACTION

  instantiation : MetaMor Env
  splat instantiation (refl , tz) x ez = aproj x tz $T (idSubst +V ez)
  mmor  instantiation K (refl , tz) f = refl , bAll (\ {k} t -> act K t (weaks K f k)) tz

  open META-ACTION instantiation

  instantiate : forall {hz n d} ->
    Term hz n d -> BAll (\ h -> Term [] (n +N h) chk) hz -> Term [] n d
  instantiate t tz = mact t (refl , tz)

  module _ where

    thinIdSubst : forall {n m}(th : n <= m) ->
      select th idSubst == (pure (_^T th) <*> idSubst)

    selectIdLemma : forall {n m}(th : n <= m) ->
      select th (pure (_^T oi o') <*> idSubst) ==
      (pure (_^T th o') <*> idSubst)
      
    selectIdLemma th =
      select th (pure (_^T oi o') <*> idSubst)
        =[ selectApp th _ _ >=
      (select th (pure (_^T oi o')) <*> select th idSubst)
        =[ reff _<*>_ =$= selectPure th _ =$= thinIdSubst th >=
      (pure (_^T oi o') <*> (pure (_^T th) <*> idSubst))
        =[ bVecMapMap _ _ _ >=
      (pure ((_^T oi o') ` (_^T th)) <*> idSubst)
        =[ bVecMapExt _ _ (\ t -> 
             (t ^T th ^T oi o')
               =< t ^T[ th - oi o' ] ]=
             (t ^T (th - oi) o')
               =[ (t ^T_) $= (_o' $= (th -oi)) >=
             (t ^T th o')
               [QED])
         idSubst >=
      (pure (_^T th o') <*> idSubst)
        [QED]

    thinIdSubst (th o') = selectIdLemma th
    thinIdSubst (th os) = reff _&_
      =$= (select th (pure (_^T oi o') <*> idSubst)
             =[ selectIdLemma th >=
           (pure (_^T th o') <*> idSubst)
             =[ bVecMapExt _ _ (\ t -> 
                (t ^T th o')
                  =< (t ^T_) $= (_o' $= (oi- th)) ]=
                (t ^T oi o' - th os)
                  =[ t ^T[ oi o' - th os ] >=
                (t ^T oi o' ^T th os)
                  [QED]) _ >=
           (pure ((_^T th os) ` (_^T oi o')) <*> idSubst)
             =< bVecMapMap _ _ _ ]=
           (pure (_^T th os) <*> (pure (_^T oi o') <*> idSubst)) [QED])
      =$= (#_ $= (_os $= oe! _ _))
    thinIdSubst oz = refl

    open META-COMMUTE Thin
      (\ { (refl , tz) th x ez ->
        (aproj x (bAll (\ {k} t -> t ^T (weaks Thin th k)) tz)
         $T (idSubst +V (pure (_^T th) <*> ez)))
          =[ (_$T _) $= aprojbAll x tz _ >=
        ((aproj x tz ^T weaks Thin th _) $T (idSubst +V (pure (_^T th) <*> ez)))
          =[ aproj x tz ^$T[ weaks Thin th _ - idSubst +V (pure (λ e → act Thin e th) <*> ez) ] >=
        (aproj x tz $T select (weaks Thin th _) (idSubst +V (pure (_^T th) <*> ez)))
          =[ (aproj x tz $T_) $= (
            select (weaks Thin th _) (idSubst +V (pure (_^T th) <*> ez))
              =[ selectWeaks th _ idSubst (pure (_^T th) <*> ez) >=
            (select th idSubst +V (pure (_^T th) <*> ez))
              =[ (_+V (pure (_^T th) <*> ez)) $= thinIdSubst th >=
            ((pure (_^T th) <*> idSubst) +V (pure (_^T th) <*> ez))
              =< bVecMapCat (_^T th) idSubst ez ]=
            (pure (_^T th) <*> (idSubst +V ez))
              [QED]
           ) >=
        (aproj x tz $T (pure (_^T th) <*> (idSubst +V ez)))
          =< aproj x tz $^T[ idSubst +V ez - th ] ]=
        act Thin (aproj x tz $T (idSubst +V ez)) th
          [QED] })
      (\ _ _ _ -> refl)
      {!!}

{-

weaksLemma : forall {n m l k}(sg : SUBST [] n m)(th : l <= k) ->
  select (oi +th th) (weaks sg k) == (pure (_^T oi +th th) <*> weaks sg l)
weaksLemma sg (th o') = 
  select (oi +th th) (pure (_^T oi o') <*> weaks sg _)
    =[ selectApp (oi +th th) _ _  >=
  (select (oi +th th) (pure (_^T oi o')) <*> select (oi +th th) (weaks sg _))
    =[ reff _<*>_ =$= selectPure (oi +th th) _ =$= weaksLemma sg th >=
  (pure (_^T oi o') <*> (pure (_^T oi +th th) <*> weaks sg _))
    =[ bVecMapMap (_^T oi o') (_^T oi +th th) _ >=
  (pure ((_^T oi o') ` (_^T oi +th th)) <*> weaks sg _)
    =[ bVecMapExt _ _ (\ t ->
         (t ^T oi +th th ^T oi o')
           =< t ^T[ oi +th th - oi o' ] ]=
         (t ^T oi +th th - oi o')
           =[ (t ^T_) $= (_o' $= (_ -oi)) >=
         (t ^T (oi +th th) o')
           [QED]
    ) (weaks sg _) >=
  (pure (_^T (oi +th th) o') <*> weaks sg _)
    [QED]
weaksLemma sg (th os) = reff _&_
  =$= (select (oi +th th) (pure (_^T oi o') <*> weaks sg _)
         =[ selectApp (oi +th th) _ _ >=
       (select (oi +th th) (pure (_^T oi o')) <*> select (oi +th th) (weaks sg _))
         =[ reff _<*>_ =$= selectPure (oi +th th) _ =$= weaksLemma sg th >=
       (pure (_^T oi o') <*> (pure (_^T oi +th th) <*> weaks sg _))
         =[ bVecMapMap (_^T oi o') (_^T oi +th th) _ >=
       (pure ((_^T oi o') ` (_^T oi +th th)) <*> weaks sg _)
         =[ bVecMapExt _ _ (\ t -> 
            (t ^T oi +th th ^T oi o')
              =< t ^T[ oi +th th - oi o' ] ]=
            (t ^T (oi +th th - oi) o')
              =[ (t ^T_) $= (_o' $= (
                 (oi +th th - oi)
                   =[ (oi +th th) -oi >=
                 (oi +th th)
                   =< oi- (oi +th th) ]=
                 (oi - oi +th th)
                   [QED])) >=
            (t ^T (oi - oi +th th) o')
              =[ t ^T[ oi o' - (oi +th th) os ] >=
            (t ^T oi o' ^T (oi +th th) os)
              [QED]
         ) (weaks sg _) >=
       (pure ((_^T (oi +th th) os) ` (_^T oi o')) <*> weaks sg _)
         =< bVecMapMap (_^T (oi +th th) os) (_^T oi o') _ ]=
       (pure (_^T (oi +th th) os) <*> (pure (_^T oi o') <*> weaks sg _))
         [QED])
  =$= (#_ $= (_os $= oe! _ _))
weaksLemma sg oz =
  select oi sg
    =[ selectoi sg >=
  sg
    =< bVecIdentity (_^T oi) _^Toi sg ]=
  (pure (_^T oi) <*> sg)
    [QED]

subEnv : forall {hz n m} -> Env hz n -> SUBST [] n m -> Env hz m
subEnv tz ez = bAll (\ {k} -> (_$T weaks ez k)) tz

inflate : forall {hz n d} -> Term [] n d -> Term hz n d
inflate ($ x) = $ x
inflate (ta , td) = inflate ta , inflate td
inflate (! t) = ! inflate t
inflate [ e ] = [ inflate e ]
inflate (() // ez)
inflate (t :: T) = inflate t :: inflate T
inflate (# i) = # i
inflate (e / s) = inflate e / inflate s

inflateLemma : forall {hz n d}(t : Term [] n d)(tz : Env hz n) -> (inflate t /T tz) == t
inflateLemma ($ x) tz = refl
inflateLemma (ta , td) tz = reff _,_ =$= inflateLemma ta tz =$= inflateLemma td tz
inflateLemma (! t) tz = !_ $= inflateLemma t _
inflateLemma [ e ] tz = [_] $= inflateLemma e tz
inflateLemma (() // ez) tz
inflateLemma (t :: T) tz = reff _::_ =$= inflateLemma t tz =$= inflateLemma T tz
inflateLemma (# i) tz = refl
inflateLemma (e / s) tz = reff _/_ =$= inflateLemma e tz =$= inflateLemma s tz

module _ where
  open Mor Subst
  
  _/$T[_-_] : forall {hz n m d}(t : Term hz n d)(tz : Env hz n)(ez : SUBST [] n m) ->
    ((t $T (pure inflate <*> ez)) /T subEnv tz ez) == ((t /T tz) $T ez)
  $ x       /$T[ tz - ez ] = refl
  (ta , td) /$T[ tz - ez ] = reff _,_ =$= (ta /$T[ tz - ez ]) =$= (td /$T[ tz - ez ])
  (! t)     /$T[ tz - ez ] = !_ $= (
          ((t $T (weak (pure inflate <*> ez))) /T bAll (_^T (oi o') +th oi) (subEnv tz ez))
             =[ {!!} >=
          ((t $T (pure inflate <*> weak ez)) /T subEnv (bAll (_^T (oi o') +th oi) tz) (weak ez))
             =[ t /$T[ _ - weak ez ] >=
          ((t /T bAll (_^T (oi o') +th oi) tz) $T weak ez)
             [QED])
  [ e ]     /$T[ tz - ez ] = [_] $= (e /$T[ tz - ez ])
  (h // fz) /$T[ tz - ez ] = {!!}
  (t :: T)  /$T[ tz - ez ] = reff _::_ =$= (t /$T[ tz - ez ]) =$= (T /$T[ tz - ez ])
  (# i)     /$T[ tz - ez ] =
    ((proj i (pure inflate <*> ez)) /T subEnv tz ez)
      =[ (_/T _) $= projApp i _ _ >=
    (proj i (pure inflate) (proj i ez) /T  bAll (_$T weaks ez _) tz)
      =[ (\ z -> z (proj i ez) /T  bAll (_$T weaks ez _) tz) $= projPure i inflate >=
    (inflate (proj i ez) /T bAll (_$T weaks ez _) tz)
      =[ inflateLemma (proj i ez) _ >=
    (proj i ez)
      [QED]
  (e / s)   /$T[ tz - ez ] = reff _/_ =$= (e /$T[ tz - ez ]) =$= (s /$T[ tz - ez ])
-}
