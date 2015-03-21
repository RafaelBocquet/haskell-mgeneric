{-# LANGUAGE DataKinds, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, PolyKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, DefaultSignatures, FlexibleContexts, InstanceSigs #-}
{-# OPTIONS_HADDOCK prune #-}


module Data.MTraversable where

import Data.MGeneric

import Control.Applicative

import Data.Unapply
import Data.HList
import Data.Proxy
import Data.Nat
import Unsafe.Coerce

-- | > AppMap ((a1 -> b1) : ...) t ~ (a1 -> t b1) : ...
type family AppMap fs t where
  AppMap '[]              t = '[]
  AppMap ((a -> b) ': fs) t = (a -> t b) ': AppMap fs t

-- | > Domain (a -> b) ~ a
--   > Domains fs ~ Map Domain fs
type family Domains fs where
  Domains '[]              = '[]
  Domains ((a -> b) ': as) = a ': Domains as
  
-- | > Codomain (a -> b) ~ b
--   > Codomains fs ~ Map Codomain fs 
type family Codomains fs where
  Codomains '[]              = '[]
  Codomains ((a -> b) ': as) = b ': Codomains as

-- | `Traversable` type class, generalisation of `Data.Traversable.Traversable`, `Data.Bitraversable.Bitraversable`, etc.
class MTraversable (f :: k) (fs :: [*]) t | fs -> k where
  -- | see `mtraverse`
  mtraverseP :: Applicative t => Proxy f -> Proxy fs -> Proxy t -> HList (AppMap fs t) -> f :$: Domains fs -> t (f :$: Codomains fs)
  default mtraverseP :: ( MGeneric (f :$: Domains fs), MGeneric (f :$: Codomains fs)
                        , Domains fs ~ Pars (f :$: Domains fs)
                        , Codomains fs ~ Pars (f :$: Codomains fs)
                        , Rep (f :$: Domains fs) ~ Rep (f :$: Codomains fs)
                        , GMTraversable (Rep (f :$: Domains fs)) fs t
                        , Applicative t
                        )
                        => Proxy f -> Proxy fs -> Proxy t -> HList (AppMap fs t) -> f :$: Domains fs -> t (f :$: Codomains fs)

  mtraverseP _ pf _ fs = fmap to . mtraverseG pf fs . from

class (AppMap fs t ~ fs') => UnAppMap fs t fs' | fs' -> fs
instance UnAppMap '[] t '[]
instance UnAppMap fs t fs' => UnAppMap ((a -> b) ': fs) t ((a -> t b) ': fs')

-- | Map elements of all type parameters of a structure to an action, evaluate these actions from left to right, and collect the results.
--
-- Proxy-less version of `mtraverseP`
--
-- Generalisation of `Data.Traversable.traverse`, `Data.Bitraversable.bitraverse`, etc.
--
-- > mtraverse :: HList '[a1 -> f b1, ..., an -> f bn] -> f a1 ... an -> t (f b1 ... bn)
mtraverse :: forall t f fs a b fs'.
             ( Applicative t
             , Unapply a f (Domains fs)
             , Unapply b f (Codomains fs)
             , UnAppMap fs t fs'
             , MTraversable f fs t
             ) => HList fs' -> a -> t b
mtraverse = mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy fs) (Proxy :: Proxy t)

type family SequenceMap as t where
   SequenceMap '[]       t = '[]
   SequenceMap (a ': as) t = (t a -> a) ': SequenceMap as t

class SequenceMapId as t where
  sequenceMapId :: Proxy as -> Proxy t -> HList (AppMap (SequenceMap as t) t)
instance SequenceMapId '[] t where
  sequenceMapId _ _ = HNil
instance SequenceMapId as t => SequenceMapId (a ': as) t where
  sequenceMapId _ pm = HCons id (sequenceMapId (Proxy :: Proxy as) pm)

-- | > msequence :: f (t a1) ... (t an) -> t (f a1 ... an)
msequence :: forall t f as a b.
             ( Applicative t
             , Unapply a f (Map t as)
             , Unapply b f as
             , Map t as ~ Domains (SequenceMap as t)
             , as ~ Codomains (SequenceMap as t)
             , MTraversable f (SequenceMap as t) t
             , SequenceMapId as t
             ) => a -> t b
msequence = mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy (SequenceMap as t)) (Proxy :: Proxy t) (sequenceMapId (Proxy :: Proxy as) (Proxy :: Proxy t))

-- Generic

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
  ExpandFieldFunction ((f :@: as) ': fs) ps = (f :$: ExpandFields as (Domains ps) -> f :$: ExpandFields as (Codomains ps)) ': ExpandFieldFunction fs ps

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
          (f :$: ExpandFields bs (Codomains fs)) ~ (f :$: Codomains (ExpandFieldFunction bs fs)),
          (f :$: ExpandFields bs (Domains fs)) ~ (f :$: Domains (ExpandFieldFunction bs fs)),
          AdaptFieldFunction bs fs t,
          AdaptFieldFunction as fs t
         )
         => AdaptFieldFunction ((f :@: bs) ': as) fs t where
  adaptFieldFunction _ pf pt fs = HCons (mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandFieldFunction bs fs)) pt (adaptFieldFunction (Proxy :: Proxy bs) pf pt fs)) (adaptFieldFunction (Proxy :: Proxy as) pf pt fs)

instance (MTraversable f (ExpandFieldFunction as fs) t,
          (f :$: ExpandFields as (Codomains fs)) ~ (f :$: Codomains (ExpandFieldFunction as fs)),
          (f :$: ExpandFields as (Domains fs)) ~ (f :$: Domains (ExpandFieldFunction as fs)),
          AdaptFieldFunction as fs t
         )
         => GFMTraversable (f :@: as) fs t where
  mtraverseGF :: Applicative t => Proxy fs -> HList (AppMap fs t) -> InField (f :@: as) (Domains fs) -> t (InField (f :@: as) (Codomains fs))
  mtraverseGF pf fs (InA a) = fmap InA (mtraverseP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandFieldFunction as fs)) (Proxy :: Proxy t) (adaptFieldFunction (Proxy :: Proxy as) pf (Proxy :: Proxy t) fs) (unsafeCoerce a))


