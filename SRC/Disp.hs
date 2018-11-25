module Disp where

import Data.Void

import Bwd

data DispEnv = DispEnv
  { intvDisp :: Bwd String
  , termDisp :: Bwd String
  }

dispE0 :: DispEnv
dispE0 = DispEnv B0 B0

class Show t => Disp t where
  disp :: DispEnv -> t -> String
  dispShow :: t -> String
  dispShow = disp dispE0
  -- I totally want Show to be an IntrinsicSuperclass

freshen :: Bwd String -> String -> String
freshen xz x = head [y | y <- x : map (x ++) [show n | n <- [0 ..]], not (elem y xz)]

instance Disp Void where
  disp _ = absurd