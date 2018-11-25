module Disp where

import Data.Void

import Bwd

data DispEnv = DispEnv
  { levs     :: Lev String
  , inxNames :: Bwd String
  }

dispE0 :: DispEnv
dispE0 = DispEnv (B0, 0) B0

class Show t => Disp t where
  disp :: DispEnv -> t -> String
  dispShow :: t -> String
  dispShow = disp dispE0
  -- I totally want Show to be an IntrinsicSuperclass

freshen :: DispEnv -> String -> (DispEnv, String)
freshen (DispEnv l@(yiz, _) xz) x = (DispEnv l (xz :< z), z) where
  z = head [y | y <- x : map (x ++) [show n | n <- [0 ..]], not (elem y zz)]
  zz = fmap fst yiz <> xz

instance Disp Void where
  disp _ = absurd