{-# LANGUAGE MultiParamTypeClasses #-}

module Intv where

import Control.Applicative

import Bind
import Bwd
import Disp
import Par

data Point
  = I0 | I1 | IP (String, Int) | IV Int | IS Point (Point, Point)
  -- the IP's Int is its de Bruijn level

instance Eq Point where
  p == q = pNorm p == pNorm q

data PNorm = IN0 | IN1 | INSP (String, Int) PNorm PNorm deriving Eq
  -- INSP invariants:
  --   the branches are distinct;
  --   the branches involve strictly lower de Bruijn levels
normP :: PNorm -> Point
normP IN0 = I0
normP IN1 = I1
normP (INSP x IN0 IN1) = IP x
normP (INSP x n0 n1) = IS (IP x) (normP n0, normP n1)

pNorm :: Point -> PNorm
pNorm I0 = IN0
pNorm I1 = IN1
pNorm (IP x) = INSP x IN0 IN1
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

instance Bind Point Point where
  stan (IV i) j p = if i == j then p else IV i
  stan I0 _ _ = I0
  stan I1 _ _ = I1
  stan (IP x) _ _ = IP x
  stan (IS pc (p0, p1)) j p = IS (stan pc j p) (stan p0 j p, stan p1 j p)
  abst f j p | f p = IV j
  abst f j (IS pc (p0, p1)) = IS (abst f j pc) (abst f j p0, abst f j p1)
  abst _ _ p = p

instance Disp Point where
  disp e (IV i) = inxNames e <? i
  disp e (IP (x, _)) = x
  disp e I0 = "0"
  disp e I1 = "1"
  disp e (IS pc (I1, I0)) = disp e pc ++ "~"
  disp e (IS pc (p0, p1)) = disp e pc ++ "{" ++ disp e p0 ++ " " ++ disp e p1 ++ "}"

instance Show Point where
  show = dispShow

pPoint :: Par Point
pPoint = pWeePoint >>= pMorePoint

pWeePoint :: Par Point
pWeePoint
  =   I0 <$ punc "0"
  <|> I1 <$ punc "1"
  <|> IV <$> pInx
  <|> IP <$> pLev

pMorePoint :: Point -> Par Point
pMorePoint p = (grow >>= pMorePoint) <|> pure p where
  grow = IS p <$ spc <*>
    (    (I0, I1) <$ punc "~"
     <|> (,) <$ punc "{" <* spc <*> pPoint
                         <* spc <*> pPoint
                         <* spc <* punc "}"
    )
