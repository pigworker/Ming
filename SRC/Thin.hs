{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Thin where

import Data.Bits
import Control.Applicative
import Control.Newtype
import Control.Monad.Identity

import Bwd
import Par
import Bind

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

os :: Thinning -> Thinning
os (Th th) = Th (shiftL th 1 .|. 1)

o' :: Thinning -> Thinning
o' (Th th) = Th (shiftL th 1)

pThinning :: Par Thinning
pThinning = pVars >>= sub where
  sub (Th i) = (Th . (i .&.) . complement . thinning) <$ spc <* punc "-" <*> pVars
           <|> pure (Th i)

pVars :: Par Thinning
pVars = foldr ((.|.) . bit) (Th 0) <$> some (spc *> pInx) <|> pure mempty

thinDom :: Thinning -> Int -> Int
thinDom _ 0 = 0
thinDom th m
  | th == mempty   = m
  | th == zeroBits = 0
thinDom th m = (if testBit th 0 then 1 else 0) + thinDom (shiftR th 1) (m - 1)

thin :: Thinning -> Int -> Int
thin th i | th == mempty   = i
          | not (testBit th 0) = 1 + thin (shiftR th 1) i
thin th 0 = 0
thin th i = 1 + thin (shiftR th 1) (i - 1)

thick :: Thinning -> Int -> Maybe Int
thick th i | th == mempty = Just i
           | th == zeroBits = Nothing
thick th 0 = if testBit th 0 then Just 0 else Nothing
thick th i = ((if testBit th 0 then 1 else 0) +) <$> thick (shiftR th 1) (i - 1)

weak :: Thinning -> Int -> Thinning
weak th 0 = th
weak th i = weak (os th) (i - 1)

thinD :: DeBruijn d => Thinning -> d LI -> d LI
thinD th = ala' (Identity .) deBruijn f 0 where
  f i (Lev x) = Lev x
  f i (Inx j) = Inx (thin (weak th i) j)

thickD :: DeBruijn d => Thinning -> d LI -> Maybe (d LI)
thickD th = deBruijn f 0 where
  f i (Lev x) = pure (Lev x)
  f i (Inx j) = Inx <$> thick (weak th i) j
