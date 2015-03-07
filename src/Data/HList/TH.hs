{-# LANGUAGE TemplateHaskell, RankNTypes, LambdaCase #-}

module Data.HList.TH where

import Data.HList

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Control.Applicative

hlist :: ExpQ -> ExpQ
hlist t = t >>= \case
  (ListE xs) -> foldr (\a b -> appE (appE (conE 'HCons) a) b) (conE 'HNil) (pure <$> xs)
  _          -> fail "hlist excepts a list"
