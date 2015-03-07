{-# LANGUAGE DataKinds, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, PolyKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, DefaultSignatures, FlexibleContexts, InstanceSigs #-}

module Data.MTraversable where

import Data.MGeneric
import Data.MGeneric.Instances

import Control.Applicative

import Data.HList
import Data.Proxy
import Data.Nat
import Unsafe.Coerce

-- Traverse

type family AppMap fs t where
  AppMap '[]              t = '[]
  AppMap ((a -> b) ': fs) t = (a -> t b) ': AppMap fs t

type family Domains fs where
  Domains '[]              = '[]
  Domains ((a -> b) ': as) = a ': Domains as
  
type family Codomains fs where
  Codomains '[]              = '[]
  Codomains ((a -> b) ': as) = b ': Codomains as

class MTraverse (f :: k) (fs :: [*]) t | fs -> k where
  mtraverse :: Applicative t => HList (AppMap fs t) -> f :$: Domains fs -> t (f :$: Codomains fs)
  mtraverse = mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy fs) (Proxy :: Proxy t)

  mtraverseP :: Applicative t => Proxy f -> Proxy fs -> Proxy t -> HList (AppMap fs t) -> f :$: Domains fs -> t (f :$: Codomains fs)
  default mtraverseP :: (MGeneric (f :$: Domains fs), MGeneric (f :$: Codomains fs),
                         Domains fs ~ Pars (f :$: Domains fs),
                         Codomains fs ~ Pars (f :$: Codomains fs),
                         Rep (f :$: Domains fs) ~ Rep (f :$: Codomains fs),
                         GMTraverse (Rep (f :$: Domains fs)) fs t,
                         Applicative t
                        )
                        => Proxy f -> Proxy fs -> Proxy t -> HList (AppMap fs t) -> f :$: Domains fs -> t (f :$: Codomains fs)

  mtraverseP _ pf _ fs = fmap to . mtraverseG pf fs . from

type family Map as t where
  Map '[]       t = '[]
  Map (a ': as) t = t a ': Map as t

type family SequenceMap as t where
   SequenceMap '[]       t = '[]
   SequenceMap (a ': as) t = (t a -> a) ': SequenceMap as t

class SequenceMapId as t where
  sequenceMapId :: Proxy as -> Proxy t -> HList (AppMap (SequenceMap as t) t)
instance SequenceMapId '[] t where
  sequenceMapId _ _ = HNil
instance SequenceMapId as t => SequenceMapId (a ': as) t where
  sequenceMapId _ pm = HCons id (sequenceMapId (Proxy :: Proxy as) pm)


class MSequence (f :: k) (as :: [*]) t | as -> k where
  msequence :: Applicative t => f :$: Map as t -> t (f :$: as)
  msequence = msequenceP (Proxy :: Proxy f) (Proxy :: Proxy as) (Proxy :: Proxy t)

  msequenceP :: Applicative t => Proxy f -> Proxy as -> Proxy t -> f :$: Map as t -> t (f :$: as)
  default msequenceP :: (Applicative t,
                         as ~ Codomains (SequenceMap as t),
                         Domains (SequenceMap as t) ~ Map as t,
                         MTraverse f (SequenceMap as t) t,
                         SequenceMapId as t
                        )
                        => Proxy f -> Proxy as -> Proxy t -> f :$: Map as t -> t (f :$: as)
  msequenceP pf pa pt = mtraverseP pf (Proxy :: Proxy (SequenceMap as t)) pt (sequenceMapId pa pt)

-- Generic

class GMTraverse (f :: Un *) (fs :: [*]) t where
  mtraverseG :: Applicative t => Proxy fs -> HList (AppMap fs t) -> In f (Domains fs) -> t (In f (Codomains fs))

instance GMTraverse UV fs t where
  mtraverseG _ _ _ = undefined

instance GMTraverse UT fs t where
  mtraverseG _ _ InT = pure InT

instance (GMTraverse u fs t, GMTraverse v fs t) => GMTraverse (u :++: v) fs t where
  mtraverseG pf fs (InL u) = fmap InL (mtraverseG pf fs u)
  mtraverseG pf fs (InR v) = fmap InR (mtraverseG pf fs v)

instance (GMTraverse u fs t, GMTraverse v fs t) => GMTraverse (u :**: v) fs t where
  mtraverseG pf fs (u :*: v) = (:*:) <$> mtraverseG pf fs u <*> mtraverseG pf fs v

instance GFMTraverse f fs t => GMTraverse (UF f) fs t where
  mtraverseG pf fs (InF f) = fmap InF (mtraverseGF pf fs f)

class GFMTraverse (f :: Field *) (fs :: [*]) t where
  mtraverseGF :: Applicative t => Proxy fs -> HList (AppMap fs t) -> InField f (Domains fs) -> t (InField f (Codomains fs))

instance GFMTraverse (FK a) fs t where
  mtraverseGF _ fs (InK a) = pure (InK a)
  
instance GFPMTraverse n fs t => GFMTraverse (FP n) fs t where
  mtraverseGF pf fs (InP a) = fmap InP (mtraverseGFP (Proxy :: Proxy n) pf fs a)

class GFPMTraverse n fs t where
  mtraverseGFP :: Applicative t => Proxy n -> Proxy fs -> HList (AppMap fs t) -> Domains fs :!: n -> t (Codomains fs :!: n)

instance GFPMTraverse NZ ((a -> b) ': as) t where
  mtraverseGFP _ _ (HCons f _) a = f a
                         
instance GFPMTraverse n as t => GFPMTraverse (NS n) ((a -> b) ': as) t where
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
 
instance (GFPMTraverse n fs t,
          AdaptFieldFunction as fs t,
          AppMap ((fs :!: n) ': ExpandFieldFunction as fs) t ~ ((Domains fs :!: n -> t (Codomains fs :!: n)) ': AppMap (ExpandFieldFunction as fs) t)
         )
         => AdaptFieldFunction (FP n ': as) fs t where
  adaptFieldFunction _ pf pt fs = HCons (mtraverseGFP (Proxy :: Proxy n) pf fs) (adaptFieldFunction (Proxy :: Proxy as) pf pt fs)

instance (MTraverse f (ExpandFieldFunction bs fs) t,
          (f :$: ExpandField bs (Codomains fs)) ~ (f :$: Codomains (ExpandFieldFunction bs fs)),
          (f :$: ExpandField bs (Domains fs)) ~ (f :$: Domains (ExpandFieldFunction bs fs)),
          AdaptFieldFunction bs fs t,
          AdaptFieldFunction as fs t
         )
         => AdaptFieldFunction ((f :@: bs) ': as) fs t where
  adaptFieldFunction _ pf pt fs = HCons (mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandFieldFunction bs fs)) pt (adaptFieldFunction (Proxy :: Proxy bs) pf pt fs)) (adaptFieldFunction (Proxy :: Proxy as) pf pt fs)

instance (MTraverse f (ExpandFieldFunction as fs) t,
          (f :$: ExpandField as (Codomains fs)) ~ (f :$: Codomains (ExpandFieldFunction as fs)),
          (f :$: ExpandField as (Domains fs)) ~ (f :$: Domains (ExpandFieldFunction as fs)),
          AdaptFieldFunction as fs t
         )
         => GFMTraverse (f :@: as) fs t where
  mtraverseGF :: Applicative t => Proxy fs -> HList (AppMap fs t) -> InField (f :@: as) (Domains fs) -> t (InField (f :@: as) (Codomains fs))
  mtraverseGF pf fs (InA a) = fmap InA (mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandFieldFunction as fs)) (Proxy :: Proxy t) (adaptFieldFunction (Proxy :: Proxy as) pf (Proxy :: Proxy t) fs) (unsafeCoerce a))


