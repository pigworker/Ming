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

record ObjMor (M : Nat -> Nat -> Set) : Set where
  field
    var : forall {n m}(i : 1 <= n)(al : M n m) -> Term [] m syn
    wkn : forall {n m} -> M n m -> M (n su) (m su)

  wkns : forall {n m}(al : M n m) k -> M (n +N k) (m +N k)
  wkns al ze = al
  wkns al (k su) = wkn (wkns al k)


-- general morphisms ---------------------------------------------------------

record Mor (M : Bwd Nat -> Nat -> Bwd Nat -> Nat -> Set) : Set where
  field
    weak : forall {hz n kz m} -> M hz n kz m -> M hz (n su) kz (m su)
    hit : forall {hz n kz m} -> (1 <= n) -> M hz n kz m -> Term kz m syn
    met : forall {hz n kz m h} -> 
            El h hz -> M hz n kz m -> BVec (Term kz m syn) h -> Term kz m chk

  act : forall {hz n kz m d} -> Term hz n d -> M hz n kz m -> Term kz m d
  actz : forall {hz n kz m h} ->
         BVec (Term hz n syn) h -> M hz n kz m -> BVec (Term kz m syn) h
  act ($ a)     m = $ a
  act (ta , td) m = act ta m , act td m
  act (! t)     m = ! act t (weak m)
  act [ e ]     m = [ act e m ]
  act (x // ez) m = met x m (actz ez m)
  act (t :: T)  m = act t m :: act T m
  act (# i)     m = hit i m
  act (e / s)   m = act e m / act s m
  actz []       m = []
  actz (ez & e) m = actz ez m & act e m

  actzLemma : forall {hz n kz m h}
    (ez : BVec (Term hz n syn) h)(m : M hz n kz m) ->
    actz ez m == (pure (\ e -> act e m) <*> ez)
  actzLemma [] m = refl
  actzLemma (ez & e) m = (_& _) $= actzLemma ez m

  actzLemma' : forall {hz n kz m h}
    (a : App' h (Term hz n syn))(m : M hz n kz m) ->
    actz (app' a) m == appN' (appNorm (pure' (\ e -> act e m) <*>' a))
  actzLemma' a m = 
    actz (app' a) m
      =[ actzLemma _ _ >=
    (pure (\ e -> act e m) <*> app' a)
      =[ appNormLemma (pure' _ <*>' a) >=
    appN' (appNorm (pure' (λ e → act e m) <*>' a))
      [QED]

module _ where

  open Mor

  data MOR (gz : Bwd Nat)(p : Nat) : Bwd Nat -> Nat -> Set1 where
    ID : MOR gz p gz p
    CO : forall {M}(K : Mor M){hz n kz m} ->
          M gz p hz n -> MOR hz n kz m -> MOR gz p kz m

  ACT : forall {hz n kz m d} -> Term hz n d -> MOR hz n kz m -> Term kz m d
  ACT t ID = t
  ACT t (CO K m M) = ACT (act K t m) M 

  WEAK : forall {hz n kz m} -> MOR hz n kz m -> MOR hz (n su) kz (m su)
  WEAK ID = ID
  WEAK (CO K m M) = CO K (weak K m) (WEAK M)

  HIT : forall {hz n kz m} -> 1 <= n -> MOR hz n kz m -> Term kz m syn
  HIT i ID = # i
  HIT i (CO K m M) = ACT (hit K i m) M

  MET' : forall {hz n kz m h} -> El h hz -> MOR hz n kz m ->
           BVec (Term hz n syn) h -> Term kz m chk
  MET' x ID ez = x // ez
  MET' x (CO K m M) ez = ACT (met K x m (pure (\ e -> act K e m) <*> ez)) M

  lemma$ : forall {hz n kz m}(a : Atom)(M : MOR hz n kz m) ->
           ACT ($ a) M == $ a
  lemma$ a ID = refl
  lemma$ a (CO K m M) = lemma$ a M

  lemma, : forall {hz n kz m}(ta td : Term hz n chk)(M : MOR hz n kz m) ->
           ACT (ta , td) M == (ACT ta M , ACT td M)
  lemma, ta td ID = refl
  lemma, ta td (CO K m M) = lemma, (act K ta m) (act K td m) M    

  lemma! : forall {hz n kz m}(t : Term hz (n su) chk)(M : MOR hz n kz m) ->
           ACT (! t) M == (! ACT t (WEAK M))
  lemma! t ID = refl
  lemma! t (CO K m M) = lemma! (act K t (weak K m)) M

  lemma[] : forall {hz n kz m}(e : Term hz n syn)(M : MOR hz n kz m) ->
             ACT [ e ] M == [ ACT e M ]
  lemma[] e ID = refl
  lemma[] e (CO K m M) = lemma[] (act K e m) M

  lemma// : forall {hz n kz m h}(x : El h hz)(ez : BVec (Term hz n syn) h) ->
             (M : MOR hz n kz m) ->
             ACT (x // ez) M == MET' x M ez
  lemma// x ez ID = refl
  lemma// x ez (CO K m M) = (\ z -> ACT (met K x m z) M) $= actzLemma K ez m

  lemma:: : forall {hz n kz m}(t T : Term hz n chk)(M : MOR hz n kz m) ->
           ACT (t :: T) M == (ACT t M :: ACT T M)
  lemma:: t T ID = refl
  lemma:: t T (CO K m M) = lemma:: (act K t m) (act K T m) M    

  lemma# : forall {hz n kz m}(i : 1 <= n)(M : MOR hz n kz m) ->
           ACT (# i) M == HIT i M
  lemma# i ID = refl
  lemma# i (CO K m M) = refl

  lemma/ : forall {hz n kz m}(e : Term hz n syn)(s : Term hz n chk)(M : MOR hz n kz m) ->
           ACT (e / s) M == (ACT e M / ACT s M)
  lemma/ e s ID = refl
  lemma/ e s (CO K m M) = lemma/ (act K e m) (act K s m) M    

  record _~M~_ {hz n kz m}(M0 M1 : MOR hz n kz m) : Set1 where
    coinductive
    field
      hitting : (i : 1 <= n) -> HIT i M0 == HIT i M1
      met'ing : forall {h}(x : El h hz)(ez : BVec (Term hz n syn) h) ->
        (pure (\ e -> ACT e M0) <*> ez) == (pure (\ e -> ACT e M1) <*> ez) ->
        MET' x M0 ez == MET' x M1 ez
      weaken : WEAK M0 ~M~ WEAK M1

  open _~M~_ public
  
  module _ where

    simulation : forall {hz n kz m d}(t : Term hz n d)
      (M0 M1 : MOR hz n kz m) -> M0 ~M~ M1 ->
      ACT t M0 == ACT t M1
    simulationz : forall {hz n kz m h}(ez : BVec (Term hz n syn) h)
      (M0 M1 : MOR hz n kz m) -> M0 ~M~ M1 ->
      (pure (\ e -> ACT e M0) <*> ez) == (pure (\ e -> ACT e M1) <*> ez)
    simulation ($ a)     M0 M1 M = 
      ACT ($ a) M0
        =[ lemma$ a M0 >=
      $ a
        =< lemma$ a M1 ]=
      ACT ($ a) M1
        [QED]
    simulation (ta , td) M0 M1 M = 
      ACT (ta , td) M0
        =[ lemma, ta td M0 >=
      (ACT ta M0 , ACT td M0)
        =[ reff _,_ =$= simulation ta M0 M1 M =$= simulation td M0 M1 M >=
      (ACT ta M1 , ACT td M1)
        =< lemma, ta td M1 ]=
      ACT (ta , td) M1
        [QED]
    simulation (! t)     M0 M1 M = 
      ACT (! t) M0
        =[ lemma! t M0 >=
      (! ACT t (WEAK M0))
        =[ !_ $= simulation t (WEAK M0) (WEAK M1) (weaken M) >=
      (! ACT t (WEAK M1))
        =< lemma! t M1 ]=
      ACT (! t) M1
        [QED]
    simulation [ e ]     M0 M1 M =
      ACT [ e ] M0
        =[ lemma[] e M0 >=
      [ ACT e M0 ]
        =[ [_] $= simulation e M0 M1 M >=
      [ ACT e M1 ]
        =< lemma[] e M1 ]=
      ACT [ e ] M1
        [QED]
    simulation (x // ez) M0 M1 M = 
      ACT (x // ez) M0
        =[ lemma// x ez M0 >=
      MET' x M0 ez
        =[ met'ing M x ez (simulationz ez M0 M1 M) >=
      MET' x M1 ez
        =< lemma// x ez M1 ]=
      ACT (x // ez) M1
        [QED]
    simulation (t :: T)  M0 M1 M =
      ACT (t :: T) M0
        =[ lemma:: t T M0 >=
      (ACT t M0 :: ACT T M0)
        =[ reff _::_ =$= simulation t M0 M1 M =$= simulation T M0 M1 M >=
      (ACT t M1 :: ACT T M1)
        =< lemma:: t T M1 ]=
      ACT (t :: T) M1
        [QED]
    simulation (# i)     M0 M1 M = 
      ACT (# i) M0
        =[ lemma# i M0 >=
      HIT i M0
        =[ hitting M i >=
      HIT i M1
        =< lemma# i M1 ]=
      ACT (# i) M1
        [QED]
    simulation (e / s)   M0 M1 M =
      ACT (e / s) M0
        =[ lemma/ e s M0 >=
      (ACT e M0 / ACT s M0)
        =[ reff _/_ =$= simulation e M0 M1 M =$= simulation s M0 M1 M >=
      (ACT e M1 / ACT s M1)
        =< lemma/ e s M1 ]=
      ACT (e / s) M1
        [QED]
    simulationz []       M0 M1 M = refl
    simulationz (ez & e) M0 M1 M =
      reff _&_ =$= simulationz ez M0 M1 M =$= simulation e M0 M1 M


-- inflation -----------------------------------------------------------------

module _ where

  open Mor

  MINFLATE : Mor \ hz n kz m -> hz == [] * (n == m)
  weak MINFLATE (refl , refl) = refl , refl
  hit  MINFLATE i (q , refl) = # i
  met  MINFLATE () (refl , q)

  _!T : forall {hz n d}(t : Term [] n d) -> Term hz n d
  t !T = act MINFLATE t (refl , refl)
  infixl 3 _!T

  inflated : forall {n hz m d}(t : Term [] n d)(M : MOR [] n hz m) ->
    ACT (t !T) M == ACT t M
  inflated t M = simulation t (CO MINFLATE (refl , refl) M) M (sim M) where
    sim : forall {n hz m} (M : MOR [] n hz m) ->
      CO MINFLATE (refl , refl) M ~M~ M
    hitting (sim M) i = lemma# i M
    met'ing (sim M) ()
    weaken  (sim M) = sim (WEAK M) 


-- from object to meta -------------------------------------------------------

data Obj (M : Nat -> Nat -> Set)(hz : Bwd Nat)(n : Nat)
  : Bwd Nat -> Nat -> Set where
  <_> : forall {m} -> M n m -> Obj M hz n hz m

module _ {M}(K : ObjMor M) where

  open ObjMor K
  open Mor

  objMor : Mor (Obj M)
  weak objMor < al >      = < wkn al >
  hit  objMor i < al >    = var i al !T
  met  objMor x < al > ez = x // ez
  
  inflationLemma : forall {hz n m d}
    (t : Term [] n d)(al : M n m) ->
    act objMor {hz} (t !T) < al > == (act objMor {[]} t < al > !T)
  inflationLemma {hz} t al = simulation t
    (CO MINFLATE (refl , refl) (CO {hz} objMor < al > ID))
    (CO objMor < al > (CO MINFLATE (refl , refl) ID))
    (sim al)
    where
    sim : forall {hz n m} (al : M n m) ->
      CO MINFLATE (refl , refl) (CO {hz} objMor < al > ID) ~M~
      CO objMor < al > (CO MINFLATE (refl , refl) ID)
    hitting (sim al) i =
      sym (inflated (var i al) (CO MINFLATE (refl , refl) ID))
    met'ing (sim al) ()
    weaken  (sim al) = sim (wkn al)


-- thinning morphisms --------------------------------------------------------

module _ where

  open ObjMor
  THIN : ObjMor _<=_
  var THIN i th = #_(i - th)
  wkn THIN th   = th os
  
  MTHIN : Mor (Obj _<=_)
  MTHIN = objMor THIN

module _ where

  open Mor MTHIN

  _^T_ : forall {hz n m d} -> Term hz n d -> n <= m -> Term hz m d
  t ^T th = act t < th >
  infixl 3 _^T_

  _^Toi : forall {hz n d}(t : Term hz n d) -> (t ^T oi) == t
  t ^Toi = simulation t (CO MTHIN < oi > ID) ID sim where
    sim : forall {n} -> CO MTHIN < oi {n} > ID ~M~ ID
    hitting sim i = #_ $= (i -oi)
    met'ing sim x ez q = (x //_) $= (
      (pure (\ e -> act e < oi >) <*> ez)
        =[ q >=
      (pure id <*> ez)
        =[ bVecIdentity _ (\ _ -> refl) ez >=
      ez
        [QED])
    weaken  sim = sim
  
  _^T[_-_] : forall {hz p n m d}(t : Term hz p d)
    (th : p <= n)(ph : n <= m) ->
    (t ^T (th - ph)) == (t ^T th ^T ph)
  t ^T[ th - ph ] = simulation t
    (CO MTHIN < th - ph > ID)
    (CO MTHIN < th > (CO MTHIN < ph > ID))
    (sim th ph) where
    sim : forall {p n m}(th : p <= n)(ph : n <= m) ->
      CO MTHIN < th - ph > ID ~M~ CO MTHIN < th > (CO MTHIN < ph > ID)
    hitting (sim th ph) i = #_ $= (i -[ th - ph ])
    met'ing (sim th ph) x ez q = (x //_) $= (
      (pure (\ e -> act e < th - ph >) <*> ez)
        =[ q >=
      (pure ((\ e -> act e < ph >) ` (\ e -> act e < th >)) <*> ez)
        =< actzLemma' (pure' _ <*>' < _ >) < ph > ]=
      actz (pure (\ e -> act e < th >) <*> ez) < ph >
        [QED])
    weaken  (sim th ph) = sim (th os) (ph os)


-- projection ----------------------------------------------------------------

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

ProjApp' : {n : Nat}{X : Set}(i : 1 <= n) -> App' n X -> X
ProjApp' i (pure' x) = x
ProjApp' i (f <*>' a) = ProjApp' i f (ProjApp' i a)
ProjApp' i < x > = proj i x

projLemma : {n : Nat}{X : Set}(i : 1 <= n)(a : App' n X) ->
  proj i (app' a) == ProjApp' i a
projLemma i (pure' x) = projPure i x
projLemma i (f <*>' a) = 
  proj i (app' (f <*>' a))
    =[ projApp i _ _ >=
  proj i (app' f) (proj i (app' a))
    =[ projLemma i f =$= projLemma i a >=
  ProjApp' i (f <*>' a)
    [QED]
projLemma i < x > = refl


-- substitution --------------------------------------------------------------

_$>_ : Nat -> Nat -> Set
n $> m = BVec (Term [] m syn) n

module _ where

  open ObjMor
  open Mor

  wksb : forall {n m} -> n $> m -> (n su) $> (m su)
  wksb sg = (pure (_^T oi o') <*> sg) & # oe os

  SUBST : ObjMor _$>_
  var SUBST i sg = proj i sg
  wkn SUBST = wksb

  MSUBST : Mor (Obj _$>_)
  MSUBST = objMor SUBST

  _$T_ : forall {hz n m d}(t : Term hz n d)(sg : n $> m) -> Term hz m d
  t $T sg = act MSUBST t < sg >
  infixl 3 _$T_


-- embedding thinnings in substitutions --------------------------------------

  thinSubst : {n m : Nat}(th : n <= m) -> n $> m
  thinSubst (th o') = pure (_^T oi o') <*> thinSubst th
  thinSubst (th os) = wksb (thinSubst th)
  thinSubst oz      = []

  thinSubstFact : forall {hz n m d}(t : Term hz n d)(th : n <= m) ->
    (t $T thinSubst th) == (t ^T th)
  thinSubstFact t th = simulation t
    (CO MSUBST < thinSubst th > ID)
    (CO MTHIN < th > ID) (sim th) where
    sim : forall {n m} (th : n <= m) ->
      CO MSUBST < thinSubst th > ID ~M~ CO MTHIN < th > ID
    hitting (sim th) i = (_!T) $= help i th where
      help : forall {n m}(i : 1 <= n)(th : n <= m) ->
        proj i (thinSubst th) == (# (i - th))
      help i (th o') =
        proj i (pure (_^T oi o') <*> thinSubst th)
          =[ projLemma i (pure' _ <*>' < _ >) >=
        (proj i (thinSubst th) ^T oi o')
          =[ ((_^T oi o') $= help i th) >=
        (# (i - th - oi o'))
          =[ #_ $= (_o' $= (_ -oi)) >=
        (# (i - th) o')
          [QED]
      help (i o') (th os) = 
        proj i (pure (_^T oi o') <*> thinSubst th)
          =[ projLemma i (pure' _ <*>' < _ >) >=
        (proj i (thinSubst th) ^T oi o')
          =[ (_^T oi o') $= help i th >=
        (# (i - th - oi o'))
          =[ #_ $= (_o' $= (_ -oi)) >=
        (# (i - th) o')
          [QED]
      help (i os) (th os) = #_ $= (_os $= oe! _ _)
      help () oz
    met'ing (sim th) x ez q = (x //_) $= q
    weaken  (sim th) = sim (th os)

  ids : forall {n} -> n $> n
  ids = thinSubst oi

  _$Tids : forall {hz n d}(t : Term hz n d) -> (t $T ids) == t
  t $Tids = 
    (t $T ids)
      =[ thinSubstFact t oi >=
    (t ^T oi)
      =[ t ^Toi >=
    t
      [QED]


-- thin then substitute ------------------------------------------------------

projSelect : forall {n m X}(i : 1 <= n)(th : n <= m)(xz : BVec X m) ->
  proj i (select th xz) == proj (i - th) xz
projSelect i (th o') (xz & x) = projSelect i th xz
projSelect (i o') (th os) (xz & x) = projSelect i th xz
projSelect (i os) (th os) (xz & x) = refl
projSelect () oz []

module _ where

  open Mor MSUBST

  _^$T[_-_] : forall {hz p n m d}(t : Term hz p d)(th : p <= n)(sg : n $> m) ->
    (t $T select th sg) == (t ^T th $T sg)
  t ^$T[ th - sg ] = simulation t
    (CO MSUBST < select th sg > ID)
    (CO MTHIN < th > (CO MSUBST < sg > ID))
    (sim th sg _ refl)
    where
    sim : forall {hz p n m}(th : p <= n)(sg : n $> m)
      (ta : p $> m)(q : ta == select th sg) ->
      CO {hz} MSUBST < ta > ID ~M~
      CO MTHIN < th > (CO MSUBST < sg > ID)
    hitting (sim th sg ._ refl) i = (_!T) $= projSelect i th sg
    met'ing (sim th sg ta _) x ez q = (x //_) $= (
      (pure (_$T ta) <*> ez)
        =[ q >=
      (pure ((_$T sg) ` (_^T th)) <*> ez)
        =< actzLemma' (pure' _ <*>' < _ >) _ ]=
      actz (pure (_^T th) <*> ez) < sg >
        [QED])
    weaken  (sim th sg ._ refl) = sim (th os) (wksb sg) _
      ((_& _) $= sym (selectLemma th (pure' _ <*>' < _ >)))



-- substitute then thingy ----------------------------------------------------

module SUBST-THINGY {M : Nat -> Nat -> Set}(K : ObjMor M) where
  module _ where
  
    open ObjMor K
    open Mor (objMor K)
    
    module RESULT
      (weakHitZero : forall {n m}(al : M n m) ->
        (# oe os) == var (oe os) (wkn al))
      (commuWeakThin : forall {n m d}(t : Term [] n d)(al : M n m) ->
        (act t < al > ^T oi o') == act (t ^T oi o') < wkn al >)
      where

      subThen : forall {p n m} -> p $> n -> M n m -> p $> m
      subThen sg al = pure (\ e -> act e < al >) <*> sg

      subThenLemma : forall {hz p n m d}(t : Term hz p d)
        (sg : p $> n)(al : M n m) ->
        (t $T subThen sg al) == act (t $T sg) < al >
      subThenLemma t sg al = simulation t
        (CO MSUBST < subThen sg al > ID)
        (CO MSUBST < sg > (CO (objMor K) < al > ID))
        (sig sg al _ refl)
        where
        sig : forall {hz p n m}(sg : p $> n)(al : M n m)(ta : p $> m) ->
          ta == subThen sg al ->
          CO {hz} MSUBST < ta > ID ~M~
          CO MSUBST < sg > (CO (objMor K) < al > ID)
        hitting (sig sg al ._ refl) i =
          (proj i (pure (\ e -> act e < al >) <*> sg) !T)
            =[ (_!T) $= projLemma i (pure' _ <*>' < _ >) >=
          (act (proj i sg) < al > !T)
            =< inflationLemma K (proj i sg) al ]=
          act (proj i sg !T) < al >
            [QED]
        met'ing (sig sg al ta q) x ez qez = (x //_) $= (
          (pure (_$T ta) <*> ez)
            =[ qez >=
          (pure (\ e -> act (e $T sg) < al >) <*> ez)
            =< actzLemma' (pure' _ <*>' < _ >) _ ]=
          actz (pure (_$T sg) <*> ez) < al >
            [QED])
        weaken  (sig sg al ._ refl) = sig (wksb sg) (wkn al) _
          (reff _&_
           =$= bVecMapMapExt _ _ _ _ (\ t -> commuWeakThin t al) _
           =$= ((_!T) $= weakHitZero al))


-- thinnings are thingies ----------------------------------------------------

module _ where

  open ObjMor THIN
  open SUBST-THINGY THIN

  commuWeakTHIN : forall {n m d}(t : Term [] n d)(th : n <= m) ->
     (t ^T th ^T oi o') == (t ^T oi o' ^T th os)
  commuWeakTHIN t th =
    (t ^T th ^T oi o')
      =< t ^T[ _ - _ ] ]=
    (t ^T (th - oi) o')
      =[ (t ^T_) $= (_o' $=
           ((th - oi) =[ th -oi >= th =< oi- th ]= (oi - th) [QED])) >=
    (t ^T (oi - th) o')
      =[ t ^T[ _ - _ ] >=
    (t ^T oi o' ^T th os)
      [QED]

  open RESULT (\ th -> #_ $= (_os $= oe! _ _)) commuWeakTHIN

  _$^T[_-_] = subThenLemma


thinSubstComp : forall {hz p n n' m d}(t : Term hz p d)
  (th : p <= n)(sg : n $> m)(ta : p $> n')(ph : n' <= m) ->
  select th sg == (pure (_^T ph) <*> ta) ->
  (t ^T th $T sg) == (t $T ta ^T ph)
thinSubstComp t th sg ta ph q =
  (t ^T th $T sg)
    =< t ^$T[ _ - _ ] ]=
  (t $T select th sg)
    =[ (t $T_) $= q >=
  (t $T (pure (_^T ph) <*> ta))
    =[ t $^T[ _ - _ ] >=
  (t $T ta ^T ph)
    [QED]



-- substitutions are thingies ------------------------------------------------

module _ where

  open ObjMor SUBST
  open SUBST-THINGY SUBST

  commuWeakSUBST : forall {n m d}(t : Term [] n d)(sg : n $> m) ->
     (t $T sg ^T oi o') == (t ^T oi o' $T wksb sg)
  commuWeakSUBST t sg = sym (thinSubstComp t _ _ _ _ (selectoi _))
      
  open RESULT (\ _ -> refl) commuWeakSUBST 

  _$T[_-_] = subThenLemma


thinLemma : forall {n m d}
    (t : Term [] n d)(ez : n $> m)(e : Term [] m syn) ->
    (t ^T oi o' $T (ez & e)) == (t $T ez)
thinLemma t ez e = 
    (t ^T oi o' $T (ez & e))
      =< t ^$T[ _ - _ ] ]=
    (t $T select oi ez)
      =[ (t $T_) $= selectoi _ >=
    (t $T ez)
      [QED]

idsComp : forall {n m}(sg : n $> m) -> (pure (_$T sg) <*> ids) == sg
idsComp [] = refl
idsComp (sg & e) = reff _&_
  =$= ((pure (_$T (sg & e)) <*> (pure (_^T oi o') <*> ids))
         =[ bVecMapMap _ _ _ (\ t -> thinLemma t _ _) _ >=
       (pure (_$T sg) <*> ids)
         =[ idsComp sg >=
       sg
         [QED])
  =$= inflated e ID


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


-- instantiations ------------------------------------------------------------

_/>_ : Bwd Nat -> Nat -> Set
hz /> n = BAll (\ h -> Term [] (n +N h) chk) hz

data Inst (hz : Bwd Nat)(n : Nat) : Bwd Nat -> Nat -> Set where
  <_> : hz /> n -> Inst hz n [] n

module ACTI {M}(K : ObjMor M) where

  open ObjMor K
  open Mor (objMor K)

  acti : forall {hz n m} -> hz /> n -> M n m -> hz /> m
  acti tz al = bAll (\ {h} t -> act t < wkns al h >) tz

module _ where

  open Mor
  
  MINST : Mor Inst
  weak MINST < tz > = < bAll (\ {h} -> (_^T (oi o' +th oi {h}))) tz >
  hit  MINST i < tz > = # i
  met  MINST x < tz > ez = aproj x tz $T (thinSubst oi +V ez)

  iactz = Mor.actz MINST

module _ where

  open Mor MINST

  _/T_ : forall {hz n d} -> Term hz n d -> hz /> n -> Term [] n d
  t /T tz = act t < tz >
  infixl 3 _/T_

  inflateInst : forall {hz n d}(t : Term [] n d)(tz : hz /> n) ->
    (t !T /T tz) == t
  inflateInst {hz} t tz = simulation t
    (CO MINFLATE (refl , refl) (CO MINST < tz > ID)) ID
    (sim tz)
    where
    sim : forall {n}(tz : hz /> n) ->
      CO MINFLATE (refl , refl) (CO MINST < tz > ID) ~M~ ID
    hitting (sim tz) i = refl
    met'ing (sim tz) () 
    weaken  (sim tz) = sim _

module _ where

  open ObjMor SUBST
  open Mor MSUBST
  open ACTI SUBST
  open _~M~_

  wknsLemma : forall {h hz n m}
      (sg : n $> m)(tz : hz /> n)(ez : BVec (Term hz n syn) h) ->
      (pure (_$T (ids +V (pure (\ e -> e /T tz $T sg) <*> ez)))
       <*> wkns sg h)
      == (pure (_$T sg) <*> (ids +V (pure (_/T tz) <*> ez)))
  wknsLemma sg _ [] = 
    (pure (_$T ids) <*> sg)
      =[ bVecIdentity (_$T ids) _$Tids sg >=
    sg
      =< idsComp sg ]=
    (pure (_$T sg) <*> ids)
      [QED]
  wknsLemma sg tz (ez & e) = reff _&_
    =$= ((pure (_$T ((ids +V (pure (\ e -> e /T tz $T sg) <*> ez)) & _))
           <*> (pure (_^T oi o') <*> wkns sg _))
          =[ bVecMapMap _ _ _ (\ t -> thinLemma t _ _) _ >=
         (pure
           (_$T (ids +V (pure (\ e -> e /T tz $T sg) <*> ez)))
           <*> wkns sg _)
          =[ wknsLemma sg tz ez >=
         (pure (_$T sg) <*> (ids +V (pure (_/T tz) <*> ez)))
           [QED])
    =$= inflated (e /T tz $T sg) ID

  wknsLemma' : forall {n m}(sg : n $> m) h ->
      select ((oi o') +th oi) (wkns (wksb sg) h) ==
      (pure (_^T (oi o') +th oi) <*> wkns sg h)
  wknsLemma' sg ze = selectoi _
  wknsLemma' sg (h su) = reff _&_
    =$= (select ((oi o') +th oi)
          (pure (_^T oi o') <*> wkns (wksb sg) h)
          =[ selectLemma ((oi o') +th oi) (pure' (_^T oi o') <*>' < wkns (wksb sg) h >) >=
        (pure (_^T oi o') <*> select ((oi o') +th oi) (wkns (wksb sg) h))
          =[ (pure (_^T oi o') <*>_) $= wknsLemma' sg h >=
        (pure (_^T oi o') <*> (pure (_^T (oi o') +th oi) <*> wkns sg h))
          =[ bVecMapMapExt _ _ _ _ (\ t -> commuWeakTHIN t _) _ >=
        (pure (_^T ((oi o') +th oi) os) <*> (pure (_^T oi o') <*> wkns sg h))
         [QED])
    =$= (#_ $= (_os $= oe! _ _))

  stable : forall {hz n m d}(t : Term hz n d)(tz : hz /> n)(sg : n $> m) ->
    (t $T sg /T acti tz sg) == (t /T tz $T sg)
  stable {hz} t tz sg = simulation t
    (CO MSUBST < sg > (CO MINST < acti tz sg > ID))
    (CO MINST < tz > (CO MSUBST < sg > ID))
    (sim tz sg _ refl)
    where
    sim : forall {n m}(tz : hz /> n)(sg : n $> m)(uz : hz /> m) ->
      uz == acti tz sg ->
      (CO MSUBST < sg > (CO MINST < uz > ID)) ~M~
      (CO MINST < tz > (CO MSUBST < sg > ID))
    hitting (sim tz sg ._ refl) i = 
        (proj i sg !T /T acti tz sg)
          =[ inflateInst (proj i sg) (acti tz sg) >=
        proj i sg
          =< inflated (proj i sg) ID ]=
        (proj i sg !T)
          [QED]
    met'ing (sim tz sg ._ refl) x ez qez =
      (aproj x (bAll (_$T wkns sg _) tz) $T
        (ids +V iactz (pure (_$T sg) <*> ez) < bAll (_$T wkns sg _) tz >))
        =[ (_$T _) $= aprojbAll x tz _ >=
      (aproj x tz $T wkns sg _ $T
        (ids +V iactz (pure (_$T sg) <*> ez) < bAll (_$T wkns sg _) tz >))
        =< aproj x tz $T[ _ - _ ] ]=
      (aproj x tz $T (pure (_$T (ids +V iactz (pure (_$T sg) <*> ez)
                                       < bAll (_$T wkns sg _) tz >))
                      <*> wkns sg _))
        =[ (aproj x tz $T_) $= (
             (pure (_$T (ids +V Mor.actz MINST (pure (_$T sg) <*> ez)
                               < bAll (_$T wkns sg _) tz >))
               <*> wkns sg _)
                =[ (\ z -> (pure (_$T (ids +V z)) <*> wkns sg _)) $= (
                   Mor.actz MINST (pure (_$T sg) <*> ez) < bAll (_$T wkns sg _) tz >
                     =[ Mor.actzLemma' MINST (pure' _ <*>' < _ >) _ >=
                   (pure (\ t -> t $T sg /T bAll (_$T wkns sg _) tz) <*> ez)
                     =[ qez >=
                   (pure (\ e -> e /T tz $T sg) <*> ez)
                     [QED]) >=
             (pure (_$T (ids +V (pure (\ e -> e /T tz $T sg) <*> ez)))
               <*> wkns sg _)
                =[ wknsLemma sg tz ez >=
             (pure (_$T sg) <*> (ids +V (pure (_/T tz) <*> ez)))
               [QED]) >=
      (aproj x tz $T (pure (_$T sg) <*> (ids +V (pure (_/T tz) <*> ez))))
        =[ aproj x tz $T[ _ - _ ] >=
      (aproj x tz $T (ids +V (pure (_/T tz) <*> ez)) $T sg)
        [QED]
    weaken (sim tz sg ._ refl) = sim _ _ _
        (bAll (\ {h} t -> t ^T (oi o' +th oi {h}))
          (bAll (\ {h} t -> act t < wkns sg h >) tz)
            =[ bAllComp _ _ _ (\ _ -> refl) _ >=
        (bAll (\ {h} t -> act t < wkns sg h > ^T (oi o' +th oi {h})) tz)
            =< bAllComp _ _ _ (\ {h} t -> thinSubstComp t _ _ _ _ (wknsLemma' sg h)) _ ]=
        bAll (\ {h} t -> act t < wkns (wkn sg) h >)
          (bAll (\ {h} t -> t ^T (oi o' +th oi {h})) tz)
            [QED])
