{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
    DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Intv where

import Control.Applicative

import Bind
import Bwd
import Disp
import Par

data Point x
  = I0 | I1 | IX x | IS (Point x) (Point x, Point x)
  deriving (Functor, Foldable, Traversable)

instance Eq (Point LI) where
  p == q = pNorm p == pNorm q

instance DeBruijn Point where
  deBruijn f i I0 = pure I0
  deBruijn f i I1 = pure I1
  deBruijn f i (IX x) = IX <$> f i x
  deBruijn f i (IS p (p0, p1)) =
    IS <$> deBruijn f i p <*> ((,) <$> deBruijn f i p0 <*> deBruijn f i p1)

data PNorm = IN0 | IN1 | INSP (String, Int) PNorm PNorm deriving Eq
  -- INSP invariants:
  --   the branches are distinct;
  --   the branches involve strictly lower de Bruijn levels
normP :: PNorm -> Point LI
normP IN0 = I0
normP IN1 = I1
normP (INSP x IN0 IN1) = IX (Lev x)
normP (INSP x n0 n1) = IS (IX (Lev x)) (normP n0, normP n1)

pNorm :: Point LI -> PNorm
pNorm I0 = IN0
pNorm I1 = IN1
pNorm (IX (Lev x)) = INSP x IN0 IN1
pNorm (IS pc (p0, p1)) = inS (pNorm pc) (pNorm p0) (pNorm p1)

inS :: PNorm -> PNorm -> PNorm -> PNorm
inS IN0 n0 _ = n0
inS IN1 _ n1 = n1
inS n n0 n1 | n0 == n1 = n0
inS p@(INSP (x, i) x0 x1) (INSP (y, j) y0 y1) n1
  | i < j  = inS (INSP (y, j) IN0 IN1) (inS p y0 n1) (inS p y1 n1)
  | i == j = inS (INSP (x, i) x0 x1) y0 n1
inS p@(INSP (x, i) x0 x1) n0 (INSP (y, j) y0 y1)
  | i < j  = inS (INSP (y, j) IN0 IN1) (inS p n0 y0) (inS p n0 y1)
  | i == j = inS (INSP (x, i) x0 x1) n0 y1
inS (INSP (x, i) x0 x1) n0 n1 = INSP (x, i) (inS x0 n0 n1) (inS x1 n0 n1)

instance Disp x => Disp (Point x) where
  disp e (IX x) = disp e x
  disp e I0 = "0"
  disp e I1 = "1"
  disp e (IS pc (I1, I0)) = disp e pc ++ "~"
  disp e (IS pc (p0, p1)) = disp e pc ++ "<" ++ disp e p0 ++ " " ++ disp e p1 ++ ">"

instance Disp x => Show (Point x) where
  show = dispShow

pPoint :: Par (Point LI)
pPoint = pWeePoint >>= pMorePoint

pWeePoint :: Par (Point LI)
pWeePoint
  =   I0 <$ punc "0"
  <|> I1 <$ punc "1"
  <|> IX <$> pLI

pMorePoint :: Point LI -> Par (Point LI)
pMorePoint p = (grow >>= pMorePoint) <|> pure p where
  grow = IS p <$ spc <*>
    (    (I0, I1) <$ punc "~"
     <|> (,) <$ punc "<" <* spc <*> pPoint
                         <* spc <*> pPoint
                         <* spc <* punc ">"
    )
