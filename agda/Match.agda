module Match where

open import Basics
open import Thinning
open import Term
open import Zipper
open import Pat

data Thicken {n m : Nat}(th : n <= m){d : Dir} : Term m d -> Set where
  thinned  : (t : Term n d) -> Thicken th (t ^T th)
  thwarted : (x : 1 <= miss th){k : Nat}(t' : Term' m k d) ->
              Thicken th (t' +T (# (x - (not th - oterm' t'))))

thwartedness : {n m : Nat}(th : n <= m){d : Dir}
  (x : 1 <= miss th){k : Nat}(t' : Term' m k d)
  (t : Term n d) -> (t ^T th) == (t' +T (# (x - (not th - oterm' t')))) -> Zero
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

depCheck : {n m : Nat}(th : n <= m){d : Dir}(t : Term m d) -> Thicken th t
depCheck th ($ x) = thinned ($ x)
depCheck th (s , t) with depCheck th s | depCheck th t
depCheck th (.(s ^T th) , .(t ^T th)) | thinned s | thinned t = thinned (s , t)
depCheck th (s , .(t' +T (# (x - (not th - oterm' t'))))) | thinned _ | thwarted x t'
  = thwarted x (s ,> t')
depCheck th (.(s' +T (# (x - (not th - oterm' s')))) , t) | thwarted x s' | _ = thwarted x (s' <, t)
depCheck th (! t) with depCheck (th os) t
depCheck th (! .(t ^T th os)) | thinned t = thinned (! t)
depCheck th (! .(t' +T (# (x - (not th o' - oterm' t'))))) | thwarted x t'
  rewrite opredLemma (not th) (oterm' t') = thwarted x (! t')
depCheck th [ e ] with depCheck th e
depCheck th [ .(e ^T th) ] | thinned e = thinned [ e ]
depCheck th [ .(e' +T (# (x - (not th - oterm' e')))) ] | thwarted x e' = thwarted x [ e' ]
depCheck th (t :: T) with depCheck th t | depCheck th T
depCheck th (.(t ^T th) :: .(T ^T th)) | thinned t | thinned T = thinned (t :: T)
depCheck th (t :: .(T' +T (# (x - (not th - oterm' T'))))) | thinned _ | thwarted x T' = thwarted x (t ::> T')
depCheck th (.(t' +T (# (x - (not th - oterm' t')))) :: T) | thwarted x t' | _ = thwarted x (t' <:: T)
depCheck th (# x) with elem? th x
depCheck th (# .(x - th)) | yes x = thinned (# x)
depCheck th (# .(x - not th)) | no x with the (Thicken th (# (x - (not th - oi)))) (thwarted x hole)
... | a rewrite not th -oi = a
depCheck th (e / s) with depCheck th e | depCheck th s
depCheck th (.(e ^T th) / .(s ^T th)) | thinned e | thinned s = thinned (e / s)
depCheck th (e / .(s' +T (# (x - (not th - oterm' s'))))) | thinned _ | thwarted x s' = thwarted x (e /> s')
depCheck th (.(e' +T (# (x - (not th - oterm' e')))) / s) | thwarted x e' | _ = thwarted x (e' </ s)

depCheckLemma :  {n m : Nat}(th : n <= m){d : Dir}(t : Term n d) -> depCheck th (t ^T th) == thinned t
depCheckLemma th ($ x) = refl
depCheckLemma th (ta , td) rewrite depCheckLemma th ta | depCheckLemma th td = refl
depCheckLemma th (! t) rewrite depCheckLemma (th os) t = refl
depCheckLemma th [ e ] rewrite depCheckLemma th e = refl
depCheckLemma th (t :: T) rewrite depCheckLemma th t | depCheckLemma th T = refl
depCheckLemma th (# x) rewrite elemLemma th x = refl
depCheckLemma th (e / s) rewrite depCheckLemma th e | depCheckLemma th s = refl

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
match? [? th ] .(t ^T (oi +th th)) | thinned t = yes t
match? [? th ] .(t' +T (# (x - (not (oi +th th) - oterm' t')))) | thwarted x t'
  = no (thwartedness (oi +th th) x t')
match? >< t = no \ ()

matchLemma : {n m : Nat}(p : Pat m)(ts : Stan p n) -> match? p (stan p ts) == yes ts
matchLemma ($ x) ts rewrite atomEqLemma x = refl
matchLemma (pa , pd) (tsa , tsd) rewrite matchLemma pa tsa | matchLemma pd tsd = refl
matchLemma (! p) ts rewrite matchLemma p ts = refl
matchLemma [? th ] t rewrite depCheckLemma (oi +th th) t = refl
matchLemma >< ()
