module Par where

import Data.Char
import Control.Monad
import Control.Applicative

import Data.Void

import Bwd
import Disp

data ParEnv = ParEnv
  { parDispEnv :: DispEnv
  , parLevs :: Lev String
  }

parInxs :: ParEnv -> Bwd String
parInxs (ParEnv (DispEnv iz) _) = iz

bindInx :: String -> ParEnv -> ParEnv
bindInx i (ParEnv (DispEnv iz) ips) = ParEnv (DispEnv (iz :< i)) ips

newtype Par t = Par {par :: ParEnv -> String -> Maybe (t, String)}

parse :: Lev String -> Par t -> String -> Maybe t
parse ips p s = do
  (t, s) <- par p (ParEnv dispE0 ips) s
  guard $ all isSpace s
  return t

instance Monad Par where
  return x = Par $ \ _ s -> Just (x, s)
  Par a >>= k = Par $ \ e s -> do
    (a, s) <- a e s
    par (k a) e s

instance Applicative Par where
  pure = return
  (<*>) = ap

instance Functor Par where
  fmap = ap . return

instance Alternative Par where
  empty = Par $ \ _ _ -> empty
  Par a <|> Par b = Par $ \ e s -> a e s <|> b e s

eat :: (Char -> Bool) -> Par Char
eat f = Par $ \ e s -> case s of
  c : s | f c -> Just (c, s)
  _ -> Nothing

pLoc :: (ParEnv -> ParEnv) -> Par x -> Par x
pLoc m (Par p) = Par (p . m)

pVoid :: Par Void
pVoid = empty

punc :: String -> Par ()
punc s = () <$ traverse (eat . (==)) s

iden :: Par String
iden = (:) <$> eat isAlpha <*> many (eat isAlphaNum)

spc :: Par ()
spc = () <$ many (eat isSpace)

pEnv :: Par ParEnv
pEnv = Par $ \ e s -> Just (e, s)

pInx :: Par Int
pInx = (parInxs <$> pEnv) >>= go where
  go B0 = empty
  go (xz :< x) = 0 <$ punc x <|> (1 +) <$> go xz

pLev :: Par (String, Int)
pLev = (levs <$> pEnv) >>= go where
  go B0 = empty
  go (xz :< (x, l)) = (x, l) <$ punc x <|> go xz
  levs (ParEnv _ (lz, _)) = lz
