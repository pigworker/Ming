{-# LANGUAGE MultiParamTypeClasses #-}

module Bind where

class Bind t s where
  stan :: t -> Int -> s -> t
  abst :: (s -> Bool) -> Int -> t -> t

