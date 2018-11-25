{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Thin where

import Data.Bits
import Control.Applicative

import Bwd
import Par

newtype Thinning = Th {thinning :: Integer} deriving (Bits, Eq, Show)

thinSel :: Bwd x -> Thinning -> ([x],[x]) -> ([x],[x])
thinSel B0 _ yn = yn
thinSel (xz :< x) (Th i) (ys, ns) = thinSel xz (Th (shiftR i 1))
  (if testBit i 0 then (x : ys, ns) else (ys, x : ns))

instance Monoid Thinning where
  mempty = complement zeroBits
  mappend th ph
    | ph == mempty = th
    | th == mempty = ph
    | ph == zeroBits = zeroBits
    | th == zeroBits = zeroBits
    | testBit ph 0 =
      let ps = shiftL (mappend (shiftR th 1) (shiftR ph 1)) 1
      in  if testBit th 0 then setBit ps 0 else ps
    | otherwise = shiftL (mappend th (shiftR ph 1)) 1
instance Semigroup Thinning where
  (<>) = mappend

pThinning :: Par Thinning
pThinning = pVars >>= sub where
  sub (Th i) = (Th . (i .&.) . complement . thinning) <$ spc <* punc "-" <*> pVars
           <|> pure (Th i)

pVars :: Par Thinning
pVars = foldr ((.|.) . bit) (Th 0) <$> some (spc *> pInx) <|> pure mempty
