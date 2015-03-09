{-# LANGUAGE DataKinds, TypeOperators, TemplateHaskell, TypeFamilies, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses #-}

module Data.MGeneric.Instances where

import Data.MGeneric
import Data.MGeneric.TH

import Data.Proxy
import Data.HList
import Data.Unapply

import Data.MFunctor
import Data.MFoldable
import Data.MTraversable

import Data.Monoid
import Control.Applicative
import Control.Monad.Identity

deriveMGeneric ''[]
deriveMGeneric ''Maybe
deriveMGeneric ''Either
deriveMGeneric ''Bool
deriveMGeneric ''Ordering
deriveMGeneric ''()
deriveMGeneric ''(,)
deriveMGeneric ''(,,)
deriveMGeneric ''(,,,)
deriveMGeneric ''(,,,,)
deriveMGeneric ''(,,,,,)
deriveMGeneric ''(,,,,,,)
deriveMGeneric ''(,,,,,,,)
deriveMGeneric ''(,,,,,,,,)
deriveMGeneric ''Last
deriveMGeneric ''First
deriveMGeneric ''Product
deriveMGeneric ''Sum
deriveMGeneric ''Endo
deriveMGeneric ''Const
deriveMGeneric ''Identity

instance MFunctor [] '[a -> a'] '[CoV]
instance MFunctor Maybe '[a -> a'] '[CoV]
instance MFunctor Either '[a -> a', b -> b'] '[CoV, CoV]
instance MFunctor Bool '[] '[]
instance MFunctor Ordering '[] '[]
instance MFunctor () '[] '[]
instance MFunctor (,) '[a -> a', b -> b'] '[CoV, CoV]
instance MFunctor (,,) '[a -> a', b -> b', c -> c'] '[CoV, CoV, CoV]
instance MFunctor (,,,) '[a -> a', b -> b', c -> c', d -> d'] '[CoV, CoV, CoV, CoV]
instance MFunctor (,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e'] '[CoV, CoV, CoV, CoV, CoV]
instance MFunctor (,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f'] '[CoV, CoV, CoV, CoV, CoV, CoV]
instance MFunctor (,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g'] '[CoV, CoV, CoV, CoV, CoV, CoV, CoV]
instance MFunctor (,,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g', h -> h'] '[CoV, CoV, CoV, CoV, CoV, CoV, CoV, CoV]
instance MFunctor (,,,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g', h -> h', i -> i'] '[CoV, CoV, CoV, CoV, CoV, CoV, CoV, CoV, CoV]
instance MFunctor Last '[a -> b] '[CoV]
instance MFunctor First '[a -> b] '[CoV]
instance MFunctor Product '[a -> b] '[CoV]
instance MFunctor Sum '[a -> b] '[CoV]
instance MFunctor (->) '[a' -> a, b -> b'] '[ContraV, CoV] where
  mmapP _ _ (HCons f (HCons g HNil)) x = g . x . f

instance MFoldMap [] '[a]
instance MFoldMap Maybe '[a]
instance MFoldMap Either '[a, b]
instance MFoldMap Bool '[]
instance MFoldMap Ordering '[]
instance MFoldMap () '[]
instance MFoldMap (,) '[a, b]
instance MFoldMap (,,) '[a, b, c]
instance MFoldMap (,,,) '[a, b, c, d]
instance MFoldMap (,,,,) '[a, b, c, d, e]
instance MFoldMap (,,,,,) '[a, b, c, d, e, f]
instance MFoldMap (,,,,,,) '[a, b, c, d, e, f, g]
instance MFoldMap (,,,,,,,) '[a, b, c, d, e, f, g, h]
instance MFoldMap (,,,,,,,,) '[a, b, c, d, e, f, g, h, i]
instance MFoldMap Last '[a]
instance MFoldMap First '[a]
instance MFoldMap Product '[a]
instance MFoldMap Sum '[a]
instance MFoldMap Identity '[a]

instance MTraverse [] '[a -> a'] t
instance MTraverse Maybe '[a -> a'] t
instance MTraverse Either '[a -> a', b -> b'] t
instance MTraverse Bool '[] t
instance MTraverse Ordering '[] t
instance MTraverse () '[] t
instance MTraverse (,) '[a -> a', b -> b'] t
instance MTraverse (,,) '[a -> a', b -> b', c -> c'] t
instance MTraverse (,,,) '[a -> a', b -> b', c -> c', d -> d'] t
instance MTraverse (,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e']  t
instance MTraverse (,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f'] t
instance MTraverse (,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g'] t
instance MTraverse (,,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g', h -> h'] t
instance MTraverse (,,,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g', h -> h', i -> i'] t
instance MTraverse Last '[a -> b] t
instance MTraverse First '[a -> b] t
instance MTraverse Product '[a -> b] t
instance MTraverse Sum '[a -> b] t
