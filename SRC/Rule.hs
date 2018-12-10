module Rule where

import Lisp
import Pat
import Elim

data Rule = Judg Pat Pat Term :- [Judg Term PVar Pat]

data Judg input subject object
  = Term :! Judg input subject object
  | Chk input subject
  | Syn input subject output
  -- ORLY?