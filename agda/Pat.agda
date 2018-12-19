module Pat where

open import Basics
open import Thinning
open import Term

data Pat (m : Nat) : Set where
  $    : Atom -> Pat m
  _,_  : Pat m -> Pat m -> Pat m
  !_   : Pat (m su) -> Pat m
  [?_] : {n : Nat} -> n <= m -> Pat m
  ><   : Pat m

_^P_ : forall {n m} -> Pat n -> n <= m -> Pat m
$ x       ^P th = $ x
(pa , pd) ^P th = pa ^P th , pd ^P th
(! p)     ^P th = ! p ^P (th os)
[? ph ]   ^P th = [? ph - th ]
><        ^P th = ><

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

stanThin : forall {k n m}(p : Pat n)(th : n <= m) ->
   (ts' : Stan (p ^P th) k) ->
   Sg (Stan p k) \ ts -> stan (p ^P th) ts' == (stan p ts ^T (oi +th th))
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
restrictStan th (pa , pd) (ta , td) (tsa , tsd) q = termNoConf q \ qa qd ->
  restrictStan th pa ta tsa qa , restrictStan th pd td tsd qd
restrictStan th (pa , pd) (! t) ts ()
restrictStan th (pa , pd) [ t ] ts ()
restrictStan th (! p) ($ x) ts ()
restrictStan th (! p) (_ , _) ts ()
restrictStan th (! p) (! t) ts q = termNoConf q \ q' -> restrictStan (th os) p t ts q'
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

patUgen : {n m : Nat}(p0 p1 : Pat m)(ts0 : Stan p0 n)(ts1 : Stan p1 n) ->
      stan p0 ts0 == stan p1 ts1 ->
      Stan (fst (patU p0 p1)) n
patUgen ($ x) ($ .x) ts0 ts1 refl rewrite atomEqLemma x = <>
patUgen ($ x) (p1 , p2) ts0 ts1 ()
patUgen ($ x) (! p1) ts0 ts1 ()
patUgen p@($ x) [? th ] ts t q = restrictStan th p t ts (sym q)
patUgen ($ x) >< ts0 () q
patUgen (p0 , p1) ($ x) ts0 ts1 ()
patUgen (pa0 , pd0) (pa1 , pd1) (tsa0 , tsd0) (tsa1 , tsd1) q = termNoConf q \ qa qd ->
  (patUgen pa0 pa1 tsa0 tsa1 qa) , (patUgen pd0 pd1 tsd0 tsd1 qd)
patUgen (p0 , p1) (! p2) ts0 ts1 ()
patUgen p@(p0 , p1) [? th ] ts t q = restrictStan th p t ts (sym q)
patUgen (p0 , p1) >< ts0 () q
patUgen (! p0) ($ x) ts0 ts1 ()
patUgen (! p0) (p1 , p2) ts0 ts1 ()
patUgen (! p0) (! p1) ts0 ts1 q = termNoConf q \ q' ->
  patUgen p0 p1 ts0 ts1 q'
patUgen p@(! p0) [? th ] ts t q = restrictStan th p t ts (sym q)
patUgen (! p0) >< ts0 () q
patUgen [? th ] p t ts1 q = restrictStan th p t ts1 q
patUgen >< p () ts1 q
