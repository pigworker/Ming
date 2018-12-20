module Pat where

open import Basics
open import Thinning
open import Term

data Pat (m : Nat) : Set where           -- m free object vars
  $    : Atom -> Pat m                   -- atoms match only themselves
  _,_  : Pat m -> Pat m -> Pat m         -- match pairwise
  !_   : Pat (m su) -> Pat m             -- match binders
  [?_] : {n : Nat} -> n <= m -> Pat m    -- match anything with permitted deps

-- thinning a pattern adds more object vars that we may not depend on
_^P_ : forall {n m} -> Pat n -> n <= m -> Pat m
$ x       ^P th = $ x
(pa , pd) ^P th = pa ^P th , pd ^P th
(! p)     ^P th = ! p ^P (th os)
[? ph ]   ^P th = [? ph - th ]

-- what does it take to instantiate a pattern?
-- a bunch of terms with some free vars and the right number of bound vars
Stan : {m : Nat} -> Pat m -> Nat -> Set
Stan ($ x)     n = One
Stan (pa , pd) n = Stan pa n * Stan pd n
Stan (! p)     n = Stan p n
Stan [? th ]   n = Term [] (n +N domo th) chk

-- instantiation plugs those terms in the holes
-- you can see it as specifying what a successful match is
stan : {m n : Nat}(p : Pat m)(ts : Stan p n) -> Term [] (n +N m) chk
stan ($ x)     <>           = $ x
stan (pa , pd) (tsa , tsd)  = stan pa tsa , stan pd tsd
stan (! p)     ts           = ! stan p ts
stan [? th ]   t            = t ^T (oi +th th)

-- lift to account for damnation
MStan : {m : Nat} -> Mebbe (Pat m) -> Nat -> Set
MStan (aye p) n = Stan p n
MStan naw     n = Zero

mstan : {m n : Nat}(p : Mebbe (Pat m))(ts : MStan p n) -> Term [] (n +N m) chk
mstan (aye p) ts = stan p ts
mstan naw     ()

-- if you can match a thinned pattern,
-- you would have matched the original
stanThin : forall {k n m}(p : Pat n)(th : n <= m) ->
   (ts' : Stan (p ^P th) k) ->
   Sg (Stan p k) \ ts -> stan (p ^P th) ts' == (stan p ts ^T (oi +th th))
stanThin ($ x) th <> = <> , refl
stanThin (pa , pd) th (tsa' , tsd') with stanThin pa th tsa' | stanThin pd th tsd'
... | tsa , qa | tsd , qd rewrite qa | qd = _ , refl
stanThin (! p) th ts' with stanThin p (th os) ts'
... | ts , q rewrite q = _ , refl
stanThin [? ph ] th t' = t' , (
  (t' ^T (oi +th (ph - th)))
    =< (t' ^T_) $= ((_+th (ph - th)) $= (oi -oi)) ]=
  (t' ^T ((oi - oi) +th (ph - th)))
    =[ (t' ^T_) $= [ oi - oi ]+th[ ph - th ] >=
  (t' ^T (oi +th ph - oi +th th))
    =[ t' ^T[ oi +th ph - oi +th th ] >=
  (t' ^T (oi +th ph) ^T (oi +th th))
    [QED])

-- Refine p r says that r is a refinement of p
-- i.e., if you match r, you definitely match p
data Refine {m : Nat} : Pat m -> Pat m -> Set where
  -- refinement follows concrete structure
  $    : (x : Atom) -> Refine ($ x) ($ x)
  _,_  : forall {pa pd ra rd} ->
         Refine pa ra -> Refine pd rd -> Refine (pa , pd) (ra , rd)
  !_   : forall {p r} -> Refine p r -> Refine (! p) (! r)
  -- but you can replace a hole by any pattern with the same deps
  [?_] : forall {n}{th : n <= m}(p : Pat n) -> Refine [? th ] (p ^P th)

-- here we show that if you match r, you match p
refiner : forall {k m : Nat}{p r : Pat m}(pr : Refine p r)(ts' : Stan r k) ->
          Sg (Stan p k) \ ts -> stan r ts' == stan p ts
refiner ($ x) <> = <> , refl
refiner (ra , rd) (tsa' , tsd') with refiner ra tsa' | refiner rd tsd'
... | tsa , qa | tsd , qd rewrite qa | qd = (tsa , tsd) , refl
refiner (! r) ts' with refiner r ts'
... | ts , q rewrite q = ts , refl
refiner [? p ] ts' with stanThin p _ ts'
... | ts , q = stan p ts , q

-- lift that to account for damnation
MRefine : {m : Nat} -> Mebbe (Pat m) -> Mebbe (Pat m) -> Set
MRefine (aye p) (aye r) = Refine p r
MRefine naw (aye x) = Zero
MRefine p naw = One

mrefiner : forall {k m : Nat}(p p' : Mebbe (Pat m))
           (r : MRefine p p')(ts' : MStan p' k) ->
               Sg (MStan p k) \ ts -> mstan p' ts' == mstan p ts
mrefiner (aye p) (aye p') r ts' = refiner r ts'
mrefiner naw (aye p') () ts'
mrefiner p naw r ()

-- one way to refine a pattern is to restrict its dependencies
restrict : {n m : Nat}(th : n <= m)(p : Pat m) -> Pat n
-- which goes structurally for concrete patterns
restrict th ($ x) = $ x
restrict th (pa , pd) = restrict th pa , restrict th pd
restrict th (! p) = ! restrict (th os) p
-- but takes the pullback of dependencies
restrict th [? ph ] = let _ , th' , ph' , ps , _ , _ = pullback th ph in [? th' ]

-- let show that, indeed, restricting dependencies then thinning is a refinement
restrictRefine : {n m : Nat}(th : n <= m)(p : Pat m) ->
                 Refine p (restrict th p ^P th)
-- the concrete cases are easy
restrictRefine th ($ x)      = $ x
restrictRefine th (pa , pd)  = restrictRefine th pa , restrictRefine th pd
restrictRefine th (! p)      = ! restrictRefine (th os) p
-- but we now need that the pullback square commutes
restrictRefine th [? ph ] with pullback th ph
... | _ , th' , ph' , ps , a , b with the (Refine [? ph ] [? ph' - ph ]) [? [? ph' ] ]
... | r rewrite triDet (mkTri ph' ph) b | triDet (mkTri th' th) a = r

-- if a thinned term matches a pattern,
-- then the original term would match the restricted pattern
restrictStan : {k n m : Nat}(th : n <= m)(p : Pat m)(t : Term [] (k +N n) chk)
               (ts : Stan p k) -> (t ^T oi +th th) == stan p ts ->
               Stan (restrict th p ^P th) k
-- yet again, the concrete structure is no trouble
restrictStan th ($ x)     t         ts          q  = <>
restrictStan th (pa , pd) ($ x)     ts          ()
restrictStan th (pa , pd) (ta , td) (tsa , tsd) q  = termNoConf q \ qa qd ->
  restrictStan th pa ta tsa qa , restrictStan th pd td tsd qd
restrictStan th (pa , pd) (! t) ts ()
restrictStan th (pa , pd) [ t ] ts ()
restrictStan th (! p)     ($ x) ts ()
restrictStan th (! p)   (_ , _) ts ()
restrictStan th (! p)     (! t) ts q = termNoConf q \ q' ->
  restrictStan (th os) p t ts q'
restrictStan th (! p) [ t ] ts ()
restrictStan _ _ (() // _) _ _
-- for pullbacks, we need that a term in the image of two thinnings
-- is in the image of the pullback
restrictStan {k} th [? ph ] t0 t1 q with thinPullback t0 (oi +th th) t1 (oi +th ph) q
... | t , q0 , q1 with pullback th ph | pullback+Lemma (oi {k}) oi th ph
... | p , _ | qp rewrite pullbackoi {k} | qp = t

patU : {m : Nat}(p0 p1 : Pat m) ->
       Sg (Mebbe (Pat m)) \ p -> MRefine (aye p0) p * MRefine (aye p1) p
patU ($ x) ($ y)  with atomEq? x y
patU ($ x) ($ .x) | yes refl = aye ($ x) , $ x , $ x
... | no _ = naw , _
patU (pa0 , pd0) (pa1 , pd1) with patU pa0 pa1
patU (pa0 , pd0) (pa1 , pd1) | aye pa , ra0 , ra1 with patU pd0 pd1
patU (pa0 , pd0) (pa1 , pd1) | aye pa , ra0 , ra1 | aye pd , rd0 , rd1 =
  aye (pa , pd) , (ra0 , rd0) , (ra1 , rd1)
patU (pa0 , pd0) (pa1 , pd1) | aye pa , ra0 , ra1 | naw , _ = naw , _
patU (pa0 , pd0) (pa1 , pd1) | naw , _ = naw , _
patU (! p0) (! p1) with patU p0 p1
patU (! p0) (! p1) | aye p , r0 , r1 = aye (! p) , (! r0) , (! r1)
patU (! p0) (! p1) | naw , _ = naw , _
patU [? th ] p1 =
  aye (restrict th p1 ^P th) , [? restrict th p1 ] , restrictRefine th p1
patU p0 [? ph ] =
  aye (restrict ph p0 ^P ph) , restrictRefine ph p0 , [? restrict ph p0 ]
patU _ _ = naw , _

patUgen : {n m : Nat}(p0 p1 : Pat m)(ts0 : Stan p0 n)(ts1 : Stan p1 n) ->
      stan p0 ts0 == stan p1 ts1 ->
      MStan (fst (patU p0 p1)) n
patUgen ($ x) ($ .x) <> <> refl rewrite atomEqLemma x = <>
patUgen ($ x) (p1 , p2) ts0 ts1 ()
patUgen ($ x) (! p1) ts0 ts1 ()
patUgen (pa0 , pd0) ($ x) ts0 ts1 ()
patUgen (pa0 , pd0) (pa1 , pd1) (tsa0 , tsd0) (tsa1 , tsd1) q =
  termNoConf q help where
  help : stan pa0 tsa0 == stan pa1 tsa1 ->
         stan pd0 tsd0 == stan pd1 tsd1 ->
         MStan (fst (patU (pa0 , pd0) (pa1 , pd1))) _
  help qa qd with patU pa0 pa1 | patUgen pa0 pa1 tsa0 tsa1 qa
  help qa qd | aye pa , _ | sa with patU pd0 pd1 | patUgen pd0 pd1 tsd0 tsd1 qd
  help qa qd | aye pa , _ | sa | aye pd , _ | sd = sa , sd
  help qa qd | aye pa , _ | _ | naw , _ | ()
  help qa qd | naw , _ | ()
patUgen (pa0 , pd0) (! p1) ts0 ts1 ()
patUgen (! p0) ($ x) ts0 ts1 ()
patUgen (! p0) (p1 , p2) ts0 ts1 ()
patUgen (! p0) (! p1) ts0 ts1 q = termNoConf q help where
  help : stan p0 ts0 == stan p1 ts1 ->
         MStan (fst (patU (! p0) (! p1))) _
  help q with patU p0 p1 | patUgen p0 p1 ts0 ts1 q
  help q | aye p , _ | s = s
  help q | naw , _ | ()
patUgen p0@($ _)   [? ph ] ts t q = restrictStan ph p0 t ts (sym q)
patUgen p0@(_ , _) [? ph ] ts t q = restrictStan ph p0 t ts (sym q)
patUgen p0@(! _)   [? ph ] ts t q = restrictStan ph p0 t ts (sym q)
patUgen [? th ] p1 t ts q = restrictStan th p1 t ts q

weaks : forall {n m} -> SUBST [] n m -> (k : Nat) -> SUBST [] (n +N k) (m +N k)
weaks sg ze = sg
weaks sg (k su) = weak (weaks sg k) where open Mor Subst

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

subStan : forall {n m k}(p : Pat k)(ts : Stan p n)(sg : SUBST [] n m) ->
  Sg (Stan p m) \ ts' -> (stan p ts $T weaks sg k) == stan p ts'
subStan ($ x) <> sg = <> , refl
subStan (pa , pd) (tsa , tsd) sg with subStan pa tsa sg | subStan pd tsd sg
... | tsa' , qa | tsd' , qd = (tsa' , tsd') , reff _,_ =$= qa =$= qd
subStan (! p) ts sg with subStan p ts sg
... | ts' , q = ts' , !_ $= q
subStan {k = k} ([?_] {l} th) t sg = (t $T weaks sg l) ,
  ((t ^T oi +th th) $T weaks sg k)
    =[ t ^$T[ oi +th th - weaks sg k ] >=
  (t $T select (oi +th th) (weaks sg k))
    =[ (t $T_) $= weaksLemma sg th >=
  (t $T (pure (_^T oi +th th) <*> weaks sg l))
    =< t $^T[ weaks sg l - oi +th th ] ]=
  ((t $T weaks sg l) ^T oi +th th)
   [QED]

patSig : forall {n} -> Pat n -> Bwd Nat
patSig ($ x) = []
patSig (pa , pd) = patSig pa +B patSig pd
patSig (! p) = patSig p
patSig [? th ] = [] & domo th

stanEnv : forall {n m}(p : Pat n) -> Stan p m -> Env (patSig p) m
stanEnv ($ x) ts = []
stanEnv (pa , pd) (tsa , tsd) = stanEnv pa tsa +A stanEnv pd tsd
stanEnv (! p) ts = stanEnv p ts
stanEnv [? th ] t = [] & t
