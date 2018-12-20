module Match where

open import Basics
open import Thinning
open import Term
open import Zipper
open import Pat

-- we define the view that tells us a term is
--   either in the image of a thinning
--   or contains an offending variable

data Thicken {n m : Nat}(th : n <= m){d : Dir} : Term [] m d -> Set where
  thinned  : (t : Term [] n d) -> Thicken th (t ^T th)
  thwarted : (x : 1 <= miss th){k : Nat}(t' : Term' m k d) ->
              Thicken th (t' +T (# (x - (not th - oterm' t'))))

-- we show these cases do not overlap
thwartedness : {n m : Nat}(th : n <= m){d : Dir}
  (x : 1 <= miss th){k : Nat}(t' : Term' m k d)
  (t : Term [] n d) -> (t ^T th) == (t' +T (# (x - (not th - oterm' t')))) -> Zero
thwartedness th x hole (# y) q with y - th | notLemma th y x
thwartedness th x hole (# y) refl | .(x - (not th - oi)) | b rewrite not th -oi
  = b refl
thwartedness th x (s' <, _) (s0 , t0) q = termNoConf q \ q0 q1 ->
  thwartedness th x s' s0 q0
thwartedness th x (_ ,> t') (s0 , t0) q = termNoConf q \ q0 q1 ->
  thwartedness th x t' t0 q1
thwartedness th x (! t') (! t) q = termNoConf q help where
  help : (t ^T th os) == (t' +T (# (x - (not th - opred (oterm' t'))))) -> Zero
  help q0 with thwartedness (th os) x t' t
  ... | b rewrite opredLemma (not th) (oterm' t') = b q0
thwartedness th x [ t' ] [ t ] q = termNoConf q (thwartedness th x t' t)
thwartedness th x (t' <:: _) (t :: _) q = termNoConf q \ q0 q1 ->
  thwartedness th x t' t q0
thwartedness th x (_ ::> T') (t :: T) q = termNoConf q \ q0 q1 ->
  thwartedness th x T' T q1
thwartedness th x (e' </ _) (e / _) q = termNoConf q \ q0 q1 ->
  thwartedness th x e' e q0
thwartedness th x (_ /> s') (_ / s) q = termNoConf q \ q0 q1 ->
  thwartedness th x s' s q1
thwartedness th x hole (t :: T) ()
thwartedness th x hole (e / s) ()
thwartedness th x (_ <, _) ($ _) ()
thwartedness th x (_ <, _) (! _) ()
thwartedness th x (_ <, _) [ _ ] ()
thwartedness th x (_ ,> _) ($ _) ()
thwartedness th x (_ ,> _) (! _) ()
thwartedness th x (_ ,> _) [ _ ] ()
thwartedness th x (! _) ($ _) ()
thwartedness th x (! _) (_ , _) ()
thwartedness th x (! _) [ _ ] ()
thwartedness th x [ _ ] ($ _) ()
thwartedness th x [ _ ] (_ , _) ()
thwartedness th x [ _ ] (! _) ()
thwartedness th x (_ <:: _) (# _) ()
thwartedness th x (_ <:: _) (_ / _) ()
thwartedness th x (_ ::> _) (# _) ()
thwartedness th x (_ ::> _) (_ / _) ()
thwartedness th x (_ </ _) (_ :: _) ()
thwartedness th x (_ </ _) (# _) ()
thwartedness th x (_ /> _) (_ :: _) ()
thwartedness th x (_ /> _) (# _) ()
thwartedness th x _ (() // _) _


-- we may now define thickening

thicken : {n m : Nat}(th : n <= m){d : Dir}(t : Term [] m d) -> Thicken th t
thicken th ($ x) = thinned ($ x)
thicken th (s , t) with thicken th s | thicken th t
thicken th (.(s ^T th) , .(t ^T th)) | thinned s | thinned t = thinned (s , t)
thicken th (s , .(t' +T (# (x - (not th - oterm' t'))))) | thinned _ | thwarted x t'
  = thwarted x (s ,> t')
thicken th (.(s' +T (# (x - (not th - oterm' s')))) , t) | thwarted x s' | _ = thwarted x (s' <, t)
thicken th (! t) with thicken (th os) t
thicken th (! .(t ^T th os)) | thinned t = thinned (! t)
thicken th (! .(t' +T (# (x - (not th o' - oterm' t'))))) | thwarted x t'
  rewrite opredLemma (not th) (oterm' t') = thwarted x (! t')
thicken th [ e ] with thicken th e
thicken th [ .(e ^T th) ] | thinned e = thinned [ e ]
thicken th [ .(e' +T (# (x - (not th - oterm' e')))) ] | thwarted x e' = thwarted x [ e' ]
thicken th (t :: T) with thicken th t | thicken th T
thicken th (.(t ^T th) :: .(T ^T th)) | thinned t | thinned T = thinned (t :: T)
thicken th (t :: .(T' +T (# (x - (not th - oterm' T'))))) | thinned _ | thwarted x T' = thwarted x (t ::> T')
thicken th (.(t' +T (# (x - (not th - oterm' t')))) :: T) | thwarted x t' | _ = thwarted x (t' <:: T)
thicken th (# x) with elem? th x
thicken th (# .(x - th)) | yes x = thinned (# x)
thicken th (# .(x - not th)) | no x with the (Thicken th (# (x - (not th - oi)))) (thwarted x hole)
... | a rewrite not th -oi = a
thicken th (e / s) with thicken th e | thicken th s
thicken th (.(e ^T th) / .(s ^T th)) | thinned e | thinned s = thinned (e / s)
thicken th (e / .(s' +T (# (x - (not th - oterm' s'))))) | thinned _ | thwarted x s' = thwarted x (e /> s')
thicken th (.(e' +T (# (x - (not th - oterm' e')))) / s) | thwarted x e' | _ = thwarted x (e' </ s)
thicken _ (() // _)


-- we prove that a thinned term can be thickened succcessfully

thickenLemma :  {n m : Nat}(th : n <= m){d : Dir}(t : Term [] n d) ->
  thicken th (t ^T th) == thinned t
thickenLemma th ($ x) = refl
thickenLemma th (ta , td) rewrite thickenLemma th ta | thickenLemma th td = refl
thickenLemma th (! t) rewrite thickenLemma (th os) t = refl
thickenLemma th [ e ] rewrite thickenLemma th e = refl
thickenLemma th (t :: T) rewrite thickenLemma th t | thickenLemma th T = refl
thickenLemma th (# x) rewrite elemLemma th x = refl
thickenLemma th (e / s) rewrite thickenLemma th e | thickenLemma th s = refl
thickenLemma th (() // _)

-- a term matches a pattern by instantiating its holes
-- or else there is no such instance

data Match? {m n : Nat}(p : Pat m) : Term [] (n +N m) chk -> Set where
  yes : (ts : Stan p n) -> Match? p (stan p ts)
  no  : {t : Term [] (n +N m) chk} ->
        ((ts : Stan p n) -> stan p ts == t -> Zero) -> Match? p t

match? : {m n : Nat}(p : Pat m)(t : Term [] (n +N m) chk) -> Match? p t
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
         _==_ {_}{Term _ _ _} (stan pa (fst ts) , stan pd (snd ts)) (stan pa tsa , td) -> Zero
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
match? [? th ] t with thicken (oi +th th) t
match? [? th ] .(t ^T (oi +th th)) | thinned t = yes t
match? [? th ] .(t' +T (# (x - (not (oi +th th) - oterm' t')))) | thwarted x t'
  = no (thwartedness (oi +th th) x t')
match? _ (() // _)

-- we prove that any instance of the pattern matches it

matchLemma : {n m : Nat}(p : Pat m)(ts : Stan p n) -> match? p (stan p ts) == yes ts
matchLemma ($ x) ts rewrite atomEqLemma x = refl
matchLemma (pa , pd) (tsa , tsd) rewrite matchLemma pa tsa | matchLemma pd tsd = refl
matchLemma (! p) ts rewrite matchLemma p ts = refl
matchLemma [? th ] t rewrite thickenLemma (oi +th th) t = refl
