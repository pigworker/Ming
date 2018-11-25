{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Thin where

import Data.Bits
import Control.Applicative

import Bwd
import Par

newtype Thinning = Th {thinning :: Integer} deriving (Bits, Eq, Show)

thI :: Thinning
thI = Th (negate 1)

thInx :: Int -> Thinning
thInx = Th . bit

thinSel :: Bwd x -> Thinning -> ([x],[x]) -> ([x],[x])
thinSel B0 _ yn = yn
thinSel (xz :< x) (Th i) (ys, ns) = thinSel xz (Th (shiftR i 1))
  (if testBit i 0 then (x : ys, ns) else (ys, x : ns))

instance Monoid Thinning where
  mempty = Th 0
  mappend = (.|.)
instance Semigroup Thinning where
  (<>) = mappend

pThinning :: Par Thinning
pThinning = pVars >>= sub where
  sub (Th i) = (Th . (i .&.) . complement . thinning) <$ spc <* punc "-" <*> pVars
           <|> pure (Th i)

pVars :: Par Thinning
pVars = foldMap thInx <$> some (spc *> pInx) <|> pure thI
