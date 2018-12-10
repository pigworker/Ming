module Par where

import Data.Char
import Control.Monad
import Control.Applicative

import Data.Void

import Bwd
import Disp
import Bind

type ParEnv = DispEnv

parInxs :: ParEnv -> Bwd String
parInxs (DispEnv _ iz) = iz

bindInx :: String -> ParEnv -> ParEnv
bindInx i (DispEnv l iz) = DispEnv l (iz :< i)

newtype Par t = Par {par :: ParEnv -> String -> Maybe (t, String)}

parse :: Lev String -> Par t -> String -> Maybe t
parse l p s = do
  (t, s) <- par p (DispEnv l B0) s
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

pLI :: Par LI
pLI = Inx <$> pInx <|> Lev <$> pLev

pInx :: Par Int
pInx = (parInxs <$> pEnv) >>= go where
  go B0 = empty
  go (xz :< x) = 0 <$ punc x <|> (1 +) <$> go xz

pLev :: Par (String, Int)
pLev = (levs <$> pEnv) >>= go where
  go B0 = empty
  go (xz :< (x, l)) = (x, l) <$ punc x <|> go xz
  levs (DispEnv (lz, _) _) = lz

pBwd :: Par x -> Par (Bwd x)
pBwd p = (p >>= \ x -> mo (B0 :< x)) <|> pure B0 where
  mo xz = ((spc *> p) >>= \ x -> mo (xz :< x)) <|> pure xz
