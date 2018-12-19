module Thinning where

open import Basics


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

_-_ : {p n m : Nat} -> p <= n -> n <= m -> p <= m
th    - ph o' = (th - ph) o'
th o' - ph os = (th - ph) o'
th os - ph os = (th - ph) os
oz    - oz    = oz
infixl 5 _-_

opred : {n m : Nat}(th : n su <= m) -> n <= m
opred (th o') = opred th o'
opred (th os) = th o'

opredLemma : {p n m : Nat}(th : p <= n)(ph : n su <= m) ->
   (th o' - ph) == (th - opred ph)
opredLemma th (ph o') rewrite opredLemma th ph = refl
opredLemma th (ph os) = refl

oe : {n : Nat} -> ze <= n
oe {ze} = oz
oe {_ su} = oe o'

oe! : {n : Nat}(x y : ze <= n) -> x == y
oe! (x o') (y o') rewrite oe! x y = refl
oe! oz oz = refl

antisym : {n m : Nat}(th : n <= m)(ph : m <= n) ->
  Sg (n == m) \ { refl -> (th == oi) * (ph == oi) }
antisym (th o') ph with antisym th (opred ph)
antisym (th o') (ph o') | refl , _ , ()
antisym (th o') (ph os) | refl , _ , ()
antisym th (ph o') with antisym (opred th) ph
antisym (th o') (ph o') | refl , () , _
antisym (th os) (ph o') | refl , () , _
antisym (th os) (ph os) with antisym th ph
antisym (.oi os) (.oi os) | refl , refl , refl = refl , refl , refl
antisym oz oz = refl , refl , refl

oi! : {n : Nat}(x y : n <= n) -> x == y
oi! x y with antisym x y
oi! x y | refl , refl , refl = refl

data Tri : {p n m : Nat}(th : p <= n)(ph : n <= m)(ps : p <= m) -> Set where
  _t-'' : {p n m : Nat}{th : p <= n}{ph : n <= m}{ps : p <= m} ->
          Tri th ph ps -> Tri th (ph o') (ps o')
  _t's' : {p n m : Nat}{th : p <= n}{ph : n <= m}{ps : p <= m} ->
          Tri th ph ps -> Tri (th o') (ph os) (ps o')
  _tsss : {p n m : Nat}{th : p <= n}{ph : n <= m}{ps : p <= m} ->
          Tri th ph ps -> Tri (th os) (ph os) (ps os)
  tzzz  : Tri oz oz oz
infixl 7 _t-'' _t's' _tsss

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

oitri : {n m : Nat}(th : n <= m) -> Tri oi th th
oitri (th o') = oitri th t-''
oitri (th os) = oitri th tsss
oitri oz = tzzz

triassoc : {q p n m : Nat}
           {th : q <= p}{ph : p <= n}{ps : q <= n}{ch : n <= m}{om : q <= m} ->
           Tri th ph ps -> Tri ps ch om ->
           Sg (p <= m) \ xi -> Tri th xi om * Tri ph ch xi
triassoc t0 (t1 t-'') with triassoc t0 t1
... | _ , t2 , t3 = _ , t2 t-'' , t3 t-''
triassoc (t0 t-'') (t1 t's') with triassoc t0 t1
... | _ , t2 , t3 = _ , t2 t-'' , t3 t's'
triassoc (t0 t's') (t1 t's') with triassoc t0 t1
... | _ , t2 , t3 = _ , t2 t's' , t3 tsss
triassoc (t0 tsss) (t1 tsss) with triassoc t0 t1
... | _ , t2 , t3 = _ , t2 tsss , t3 tsss
triassoc tzzz tzzz = oz , tzzz , tzzz
           
oi-_ : {n m : Nat}(th : n <= m) -> (oi - th) == th
oi- th = triDet (mkTri oi th) (oitri th)

_-oi : {n m : Nat}(th : n <= m) -> (th - oi) == th
th -oi = triDet (mkTri th oi) (trioi th)

_-[_-_] : {q p n m : Nat}(th : q <= p)(ph : p <= n)(ps : n <= m) ->
          (th - (ph - ps)) == ((th - ph) - ps)
th -[ ph - ps ] with triassoc (mkTri th ph) (mkTri (th - ph) ps)
... | ch , t0 , t1 rewrite triDet (mkTri ph ps) t1 = triDet (mkTri th ch) t0 

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

_+Tri_ : {p n m : Nat}{th : p <= n}{ph : n <= m}{ps : p <= m}(x : Tri th ph ps)
         {p' n' m' : Nat}{th' : p' <= n'}{ph' : n' <= m'}{ps' : p' <= m'}(y : Tri th' ph' ps')
         ->
         Tri (th +th th') (ph +th ph') (ps +th ps')
x +Tri (y t-'') = (x +Tri y) t-''
x +Tri (y t's') = (x +Tri y) t's'
x +Tri (y tsss) = (x +Tri y) tsss
x +Tri tzzz = x

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

