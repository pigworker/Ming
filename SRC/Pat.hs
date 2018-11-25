module Pat where

import Control.Applicative
import Data.List

import Bwd
import Disp
import Par
import Lisp
import Thin

type Pat = Lisp PVar

pPat :: Par Pat
pPat = pLisp pPVar

data PVar = String :? Thinning deriving Show

pPVar :: Par PVar
pPVar = (:?) <$> iden <*> pThinning

instance Disp PVar where
  disp (DispEnv _ xz) (m :? th) = m ++ case thinSel xz th ([],[]) of
    (_, []) -> ""
    ([], _) -> "-"
    (ys, ns) -> let ys' = " " ++ intercalate " " ys
                    ns' = "-" ++ intercalate " " ns
                in if length ys' >= length ns' then ys' else ns'


