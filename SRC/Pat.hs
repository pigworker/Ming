{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
    KindSignatures #-}

module Pat where

import Control.Applicative
import Data.List
import Control.Newtype

import Bwd
import Disp
import Par
import Lisp
import Thin
import Bind
import Nope

type Pat = Lisp PVar Nope

pPat :: Par (Pat LI)
pPat = pLisp pPVar pNope

data PVar (f :: * -> *) x
  = String :? Thinning
  deriving (Show, Functor, Foldable, Traversable)

instance DeBruijn (PVar f) where
  deBruijn f i (x :? th) = pure (x :? th)

pPVar :: Par (PVar f x)
pPVar = (:?) <$> iden <*> pThinning

instance Disp (PVar f x) where
  disp (DispEnv _ xz) (m :? th) = m ++ case thinSel xz th ([],[]) of
    (_, []) -> ""
    ([], _) -> "-"
    (ys, ns) -> let ys' = " " ++ intercalate " " ys
                    ns' = "-" ++ intercalate " " ns
                in (if length ys' >= length ns' then ys' else ns')

patDom :: Int -> Pat LI -> Bwd (Int, String)
patDom i (A _) = B0
patDom i (a :& d) = patDom i a <> patDom i d
patDom i (_ :. B p) = patDom (i + 1) p
patDom i (P _) = B0
patDom i (Pa n) = nope n
patDom i (Br (x :? th)) = B0 :< (thinDom th i, x)

patMat :: (DeBruijn (pa (Lisp br pa)), DeBruijn (br (Lisp br pa))) =>
          Int -> Pat LI -> Lisp br pa LI ->
          Maybe (Bwd ((Int, String), Lisp br pa LI))
patMat _ (A x) (A y) | x == y = return B0
patMat i (ap :& dp) (at :& dt) = (<>) <$> patMat i ap at <*> patMat i dp dt
patMat i (_ :. B bp) (_ :. B bt) = patMat (i + 1) bp bt
patMat i (Br (x :? th)) t = (B0 :<) <$> ((,) (thinDom th i, x) <$> thickD th t)
patMat i _ _ = Nothing
