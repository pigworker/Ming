module Par where

import Data.Char
import Control.Monad
import Control.Applicative

import Data.Void

import Bwd
import Disp

data ParEnv = ParEnv
  { parDispEnv :: DispEnv
  , parIPs :: Lev String
  }

bindI :: String -> ParEnv -> ParEnv
bindI i (ParEnv (DispEnv iz xz) ips) = ParEnv (DispEnv (iz :< i) xz) ips

seekI :: ParEnv -> Bwd String
seekI (ParEnv (DispEnv iz _) _) = iz

bindX :: String -> ParEnv -> ParEnv
bindX x (ParEnv (DispEnv iz xz) ips) = ParEnv (DispEnv iz (xz :< x)) ips

seekX :: ParEnv -> Bwd String
seekX (ParEnv (DispEnv _ xz) _) = xz


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

pInx :: (ParEnv -> Bwd String) -> Par Int
pInx g = (g <$> pEnv) >>= go where
  go B0 = empty
  go (xz :< x) = 0 <$ punc x <|> (1 +) <$> go xz

pLev :: (ParEnv -> Lev String) -> Par (String, Int)
pLev g = (g <$> pEnv) >>= (go . fst) where
  go B0 = empty
  go (xz :< (x, l)) = (x, l) <$ punc x <|> go xz

