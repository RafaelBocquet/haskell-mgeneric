{-# LANGUAGE DataKinds, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, PolyKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, DefaultSignatures, FlexibleContexts, InstanceSigs #-}

module Data.MTraversable where

import Data.MGeneric
import Data.MGeneric.Instances

import Control.Applicative

import Data.HList
import Data.Proxy
import Data.Nat
import Unsafe.Coerce

type family AppMap fs t where
  AppMap '[]              t = '[]
  AppMap ((a -> b) ': fs) t = (a -> t b) ': AppMap fs t

type family Domains fs where
  Domains '[]              = '[]
  Domains ((a -> b) ': as) = a ': Domains as
  
type family Codomains fs where
  Codomains '[]              = '[]
  Codomains ((a -> b) ': as) = b ': Codomains as

class MTraversable (f :: k) (fs :: [*]) t | fs -> k where
  mtraverse :: Applicative t => HList (AppMap fs t) -> f :$: Domains fs -> t (f :$: Codomains fs)
  mtraverse = mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy fs) (Proxy :: Proxy t)

  mtraverseP :: Applicative t => Proxy f -> Proxy fs -> Proxy t -> HList (AppMap fs t) -> f :$: Domains fs -> t (f :$: Codomains fs)
  default mtraverseP :: (MGeneric (f :$: Domains fs), MGeneric (f :$: Codomains fs),
                         Domains fs ~ Pars (f :$: Domains fs),
                         Codomains fs ~ Pars (f :$: Codomains fs),
                         Rep (f :$: Domains fs) ~ Rep (f :$: Codomains fs),
                         GMTraversable (Rep (f :$: Domains fs)) fs t,
                         Applicative t
                        )
                        => Proxy f -> Proxy fs -> Proxy t -> HList (AppMap fs t) -> f :$: Domains fs -> t (f :$: Codomains fs)

  mtraverseP _ pf _ fs = fmap to . mtraverseG pf fs . from

class GMTraversable (f :: Un *) (fs :: [*]) t where
  mtraverseG :: Applicative t => Proxy fs -> HList (AppMap fs t) -> In f (Domains fs) -> t (In f (Codomains fs))

instance GMTraversable UV fs t where
  mtraverseG _ _ _ = undefined

instance GMTraversable UT fs t where
  mtraverseG _ _ InT = pure InT

instance (GMTraversable u fs t, GMTraversable v fs t) => GMTraversable (u :++: v) fs t where
  mtraverseG pf fs (InL u) = fmap InL (mtraverseG pf fs u)
  mtraverseG pf fs (InR v) = fmap InR (mtraverseG pf fs v)

instance (GMTraversable u fs t, GMTraversable v fs t) => GMTraversable (u :**: v) fs t where
  mtraverseG pf fs (u :*: v) = (:*:) <$> mtraverseG pf fs u <*> mtraverseG pf fs v

instance GFMTraversable f fs t => GMTraversable (UF f) fs t where
  mtraverseG pf fs (InF f) = fmap InF (mtraverseGF pf fs f)

class GFMTraversable (f :: Field *) (fs :: [*]) t where
  mtraverseGF :: Applicative t => Proxy fs -> HList (AppMap fs t) -> InField f (Domains fs) -> t (InField f (Codomains fs))

instance GFMTraversable (FK a) fs t where
  mtraverseGF _ fs (InK a) = pure (InK a)
  
instance GFPMTraversable n fs t => GFMTraversable (FP n) fs t where
  mtraverseGF pf fs (InP a) = fmap InP (mtraverseGFP (Proxy :: Proxy n) pf fs a)

class GFPMTraversable n fs t where
  mtraverseGFP :: Applicative t => Proxy n -> Proxy fs -> HList (AppMap fs t) -> Domains fs :!: n -> t (Codomains fs :!: n)

instance GFPMTraversable NZ ((a -> b) ': as) t where
  mtraverseGFP _ _ (HCons f _) a = f a
                         
instance GFPMTraversable n as t => GFPMTraversable (NS n) ((a -> b) ': as) t where
  mtraverseGFP _ _ (HCons _ fs) a = mtraverseGFP (Proxy :: Proxy n) (Proxy :: Proxy as) fs a

type family ExpandFieldFunction (f :: [Field *]) (ps :: [*]) :: [*] where
  ExpandFieldFunction '[]          ps       = '[]
  ExpandFieldFunction (FK a ': fs) ps       = (a -> a) ': ExpandFieldFunction fs ps
  ExpandFieldFunction (FP n ': fs) ps       = (ps :!: n) ': ExpandFieldFunction fs ps
  ExpandFieldFunction ((f :@: as) ': fs) ps = (f :$: ExpandField as (Domains ps) -> f :$: ExpandField as (Codomains ps)) ': ExpandFieldFunction fs ps

class AdaptFieldFunction (f :: [Field *]) (fs :: [*]) t where
  adaptFieldFunction :: Applicative t => Proxy f -> Proxy fs -> Proxy t -> HList (AppMap fs t) -> HList (AppMap (ExpandFieldFunction f fs) t)
  
instance AdaptFieldFunction '[] fs t where
  adaptFieldFunction _ _ _ fs = HNil
         
instance AdaptFieldFunction as fs t => AdaptFieldFunction (FK a ': as) fs t where
  adaptFieldFunction _ pf pt fs = HCons pure (adaptFieldFunction (Proxy :: Proxy as) pf pt fs)
 
instance (GFPMTraversable n fs t,
          AdaptFieldFunction as fs t,
          AppMap ((fs :!: n) ': ExpandFieldFunction as fs) t ~ ((Domains fs :!: n -> t (Codomains fs :!: n)) ': AppMap (ExpandFieldFunction as fs) t)
         )
         => AdaptFieldFunction (FP n ': as) fs t where
  adaptFieldFunction _ pf pt fs = HCons (mtraverseGFP (Proxy :: Proxy n) pf fs) (adaptFieldFunction (Proxy :: Proxy as) pf pt fs)

instance (MTraversable f (ExpandFieldFunction bs fs) t,
          (f :$: ExpandField bs (Codomains fs)) ~ (f :$: Codomains (ExpandFieldFunction bs fs)),
          (f :$: ExpandField bs (Domains fs)) ~ (f :$: Domains (ExpandFieldFunction bs fs)),
          AdaptFieldFunction bs fs t,
          AdaptFieldFunction as fs t
         )
         => AdaptFieldFunction ((f :@: bs) ': as) fs t where
  adaptFieldFunction _ pf pt fs = HCons (mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandFieldFunction bs fs)) pt (adaptFieldFunction (Proxy :: Proxy bs) pf pt fs)) (adaptFieldFunction (Proxy :: Proxy as) pf pt fs)

instance (MTraversable f (ExpandFieldFunction as fs) t,
          (f :$: ExpandField as (Codomains fs)) ~ (f :$: Codomains (ExpandFieldFunction as fs)),
          (f :$: ExpandField as (Domains fs)) ~ (f :$: Domains (ExpandFieldFunction as fs)),
          AdaptFieldFunction as fs t
         )
         => GFMTraversable (f :@: as) fs t where
  mtraverseGF :: Applicative t => Proxy fs -> HList (AppMap fs t) -> InField (f :@: as) (Domains fs) -> t (InField (f :@: as) (Codomains fs))
  mtraverseGF pf fs (InA a) = fmap InA (mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandFieldFunction as fs)) (Proxy :: Proxy t) (adaptFieldFunction (Proxy :: Proxy as) pf (Proxy :: Proxy t) fs) (unsafeCoerce a))

