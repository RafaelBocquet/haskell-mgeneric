{-# LANGUAGE DataKinds, TypeOperators, TemplateHaskell, TypeFamilies, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances #-}

module Data.MGeneric.Instances where

import Data.MGeneric
import Data.MGeneric.TH

import Data.Proxy
import Data.HList
import Data.Nat
import Data.Unapply
import Data.HList.TH

import Data.MFunctor
import Data.MFoldable
import Data.MTraversable
import Data.MZip

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

instance MFunctor [] '[a -> a'] '[ 'CoV]
instance MFunctor Maybe '[a -> a'] '[ 'CoV]
instance MFunctor Either '[a -> a', b -> b'] '[ 'CoV, 'CoV]
instance MFunctor Bool '[] '[]
instance MFunctor Ordering '[] '[]
instance MFunctor () '[] '[]
instance MFunctor (,) '[a -> a', b -> b'] '[ 'CoV, 'CoV]
instance MFunctor (,,) '[a -> a', b -> b', c -> c'] '[ 'CoV, 'CoV, 'CoV]
instance MFunctor (,,,) '[a -> a', b -> b', c -> c', d -> d'] '[ 'CoV, 'CoV, 'CoV, 'CoV]
instance MFunctor (,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e'] '[ 'CoV, 'CoV, 'CoV, 'CoV, 'CoV]
instance MFunctor (,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f'] '[ 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV]
instance MFunctor (,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g'] '[ 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV]
instance MFunctor (,,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g', h -> h'] '[ 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV]
instance MFunctor (,,,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g', h -> h', i -> i'] '[ 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV, 'CoV]
instance MFunctor Last '[a -> b] '[ 'CoV]
instance MFunctor First '[a -> b] '[ 'CoV]
instance MFunctor Product '[a -> b] '[ 'CoV]
instance MFunctor Sum '[a -> b] '[ 'CoV]
instance MFunctor (->) '[a' -> a, b -> b'] '[ 'ContraV, 'CoV] where
  mmapP _ _ (HCons f (HCons g HNil)) x = g . x . f

-- instance (Functor/Contravariant/Bifunctor/Profunctor) f => MFunctor would be nice, but it breaks functional dependencies

instance MFoldable [] '[a]
instance MFoldable Maybe '[a]
instance MFoldable Either '[a, b]
instance MFoldable Bool '[]
instance MFoldable Ordering '[]
instance MFoldable () '[]
instance MFoldable (,) '[a, b]
instance MFoldable (,,) '[a, b, c]
instance MFoldable (,,,) '[a, b, c, d]
instance MFoldable (,,,,) '[a, b, c, d, e]
instance MFoldable (,,,,,) '[a, b, c, d, e, f]
instance MFoldable (,,,,,,) '[a, b, c, d, e, f, g]
instance MFoldable (,,,,,,,) '[a, b, c, d, e, f, g, h]
instance MFoldable (,,,,,,,,) '[a, b, c, d, e, f, g, h, i]
instance MFoldable Last '[a]
instance MFoldable First '[a]
instance MFoldable Product '[a]
instance MFoldable Sum '[a]
instance MFoldable Identity '[a]

instance MTraversable [] '[a -> a'] t
instance MTraversable Maybe '[a -> a'] t
instance MTraversable Either '[a -> a', b -> b'] t
instance MTraversable Bool '[] t
instance MTraversable Ordering '[] t
instance MTraversable () '[] t
instance MTraversable (,) '[a -> a', b -> b'] t
instance MTraversable (,,) '[a -> a', b -> b', c -> c'] t
instance MTraversable (,,,) '[a -> a', b -> b', c -> c', d -> d'] t
instance MTraversable (,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e']  t
instance MTraversable (,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f'] t
instance MTraversable (,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g'] t
instance MTraversable (,,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g', h -> h'] t
instance MTraversable (,,,,,,,,) '[a -> a', b -> b', c -> c', d -> d', e -> e', f -> f', g -> g', h -> h', i -> i'] t
instance MTraversable Last '[a -> b] t
instance MTraversable First '[a -> b] t
instance MTraversable Product '[a -> b] t
instance MTraversable Sum '[a -> b] t

instance ( MZipWithG n [] (Rep ([] :$: LCodoms n '[f])) '[f]
         , GMZipWith n (Rep ([] :$: LCodoms n '[f])) '[f]
         ) => MZipWith n [] '[f]
instance ( MZipWithG n Maybe (Rep (Maybe :$: LCodoms n '[f])) '[f]
         , GMZipWith n (Rep (Maybe :$: LCodoms n '[f])) '[f]
         ) => MZipWith n Maybe '[f]
instance ( MZipWithG n Either (Rep (Either :$: LCodoms n '[f, g])) '[f, g]
         , GMZipWith n (Rep (Either :$: LCodoms n '[f, g])) '[f, g]
         ) => MZipWith n Either '[f, g]
instance ( MZipWithG n Bool (Rep (Bool :$: LCodoms n '[])) '[]
         , GMZipWith n (Rep (Bool :$: LCodoms n '[])) '[]
         ) => MZipWith n Bool '[]
instance ( MZipWithG n Ordering (Rep (Ordering :$: LCodoms n '[])) '[]
         , GMZipWith n (Rep (Ordering :$: LCodoms n '[])) '[]
         ) => MZipWith n Ordering '[]
instance ( MZipWithG n () (Rep (() :$: LCodoms n '[])) '[]
         , GMZipWith n (Rep (() :$: LCodoms n '[])) '[]
         ) => MZipWith n () '[]
instance ( MZipWithG n (,) (Rep ((,) :$: LCodoms n '[f, g])) '[f, g]
         , GMZipWith n (Rep ((,) :$: LCodoms n '[f, g])) '[f, g]
         ) => MZipWith n (,) '[f, g]
instance ( MZipWithG n (,,) (Rep ((,,) :$: LCodoms n '[f, g, h])) '[f, g, h]
         , GMZipWith n (Rep ((,,) :$: LCodoms n '[f, g, h])) '[f, g, h]
         ) => MZipWith n (,,) '[f, g, h]
instance ( MZipWithG n (,,,) (Rep ((,,,) :$: LCodoms n '[f, g, h, i])) '[f, g, h, i]
         , GMZipWith n (Rep ((,,,) :$: LCodoms n '[f, g, h, i])) '[f, g, h, i]
         ) => MZipWith n (,,,) '[f, g, h, i]
instance ( MZipWithG n (,,,,) (Rep ((,,,,) :$: LCodoms n '[f, g, h, i, j])) '[f, g, h, i, j]
         , GMZipWith n (Rep ((,,,,) :$: LCodoms n '[f, g, h, i, j])) '[f, g, h, i, j]
         ) => MZipWith n (,,,,) '[f, g, h, i, j]
instance ( MZipWithG n (,,,,,) (Rep ((,,,,,) :$: LCodoms n '[f, g, h, i, j, k])) '[f, g, h, i, j, k]
         , GMZipWith n (Rep ((,,,,,) :$: LCodoms n '[f, g, h, i, j, k])) '[f, g, h, i, j, k]
         ) => MZipWith n (,,,,,) '[f, g, h, i, j, k]
instance ( MZipWithG n (,,,,,,) (Rep ((,,,,,,) :$: LCodoms n '[f, g, h, i, j, k, l])) '[f, g, h, i, j, k, l]
         , GMZipWith n (Rep ((,,,,,,) :$: LCodoms n '[f, g, h, i, j, k, l])) '[f, g, h, i, j, k, l]
         ) => MZipWith n (,,,,,,) '[f, g, h, i, j, k, l]
instance ( MZipWithG n (,,,,,,,) (Rep ((,,,,,,,) :$: LCodoms n '[f, g, h, i, j, k, l, m])) '[f, g, h, i, j, k, l, m]
         , GMZipWith n (Rep ((,,,,,,,) :$: LCodoms n '[f, g, h, i, j, k, l, m])) '[f, g, h, i, j, k, l, m]
         ) => MZipWith n (,,,,,,,) '[f, g, h, i, j, k, l, m]
instance ( MZipWithG n (,,,,,,,,) (Rep ((,,,,,,,,) :$: LCodoms n '[f, g, h, i, j, k, l, m, o])) '[f, g, h, i, j, k, l, m, o]
         , GMZipWith n (Rep ((,,,,,,,,) :$: LCodoms n '[f, g, h, i, j, k, l, m, o])) '[f, g, h, i, j, k, l, m, o]
         ) => MZipWith n (,,,,,,,,) '[f, g, h, i, j, k, l, m, o]
instance ( MZipWithG n Product (Rep (Product :$: LCodoms n '[f])) '[f]
         , GMZipWith n (Rep (Product :$: LCodoms n '[f])) '[f]
         ) => MZipWith n Product '[f]
instance ( MZipWithG n Sum (Rep (Sum :$: LCodoms n '[f])) '[f]
         , GMZipWith n (Rep (Sum :$: LCodoms n '[f])) '[f]
         ) => MZipWith n Sum '[f]
instance ( MZipWithG n Last (Rep (Last :$: LCodoms n '[f])) '[f]
         , GMZipWith n (Rep (Last :$: LCodoms n '[f])) '[f]
         ) => MZipWith n Last '[f]
instance ( MZipWithG n First (Rep (First :$: LCodoms n '[f])) '[f]
         , GMZipWith n (Rep (First :$: LCodoms n '[f])) '[f]
         ) => MZipWith n First '[f]


