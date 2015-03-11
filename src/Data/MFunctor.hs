{-# LANGUAGE DataKinds, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, PolyKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, DefaultSignatures, FlexibleContexts #-}

module Data.MFunctor where

import Data.MGeneric
import Data.Unapply

import Data.HList
import Data.Proxy
import Data.Nat
import Unsafe.Coerce

data Variance = CoV | ContraV

type family Domains fs vs where
  Domains '[]              '[]             = '[]
  Domains ((a -> b) ': as) (CoV ': vs)     = a ': Domains as vs
  Domains ((a -> b) ': as) (ContraV ': vs) = b ': Domains as vs
  
type family Codomains fs vs where
  Codomains '[]              '[]             = '[]
  Codomains ((a -> b) ': as) (CoV ': vs)     = b ': Codomains as vs
  Codomains ((a -> b) ': as) (ContraV ': vs) = a ': Codomains as vs

type family Flip f where
  Flip (a -> b) = (b -> a)

class MFunctor (f :: k) (fs :: [*]) (vs ::  [Variance]) | f -> vs, fs -> k, vs -> k where
  mmapP :: Proxy f -> Proxy vs -> HList fs -> f :$: Domains fs vs -> f :$: Codomains fs vs
  default mmapP :: ( MGeneric (f :$: Domains fs vs), MGeneric (f :$: Codomains fs vs),
                     Rep (f :$: Domains fs vs) ~ Rep (f :$: Codomains fs vs),
                     Domains fs vs ~ Pars (f :$: Domains fs vs),
                     Codomains fs vs ~ Pars (f :$: Codomains fs vs),
                     GMFunctor (Rep (f :$: Domains fs vs)) fs vs
                   ) => Proxy f -> Proxy vs -> HList fs -> f :$: Domains fs vs -> f :$: Codomains fs vs
  mmapP _ pv fs = to . mmapG pv fs . from

mmap :: forall a b f fs vs.
        ( Unapply a f (Domains fs vs),
          Unapply b f (Codomains fs vs),
          MFunctor f fs vs
        ) => HList fs -> a -> b
mmap = mmapP (Proxy :: Proxy f) (Proxy :: Proxy vs)

class GMFunctor (f :: Un *) (fs :: [*]) (vs :: [Variance]) where
  mmapG :: Proxy vs -> HList fs -> In f (Domains fs vs) -> In f (Codomains fs vs)

instance GMFunctor UV fs vs where
  mmapG _ _ _ = undefined

instance GMFunctor UT fs vs where
  mmapG _ _ InT = InT

instance (GMFunctor u fs vs, GMFunctor v fs vs) => GMFunctor (u :++: v) fs vs where
  mmapG pv fs (InL u) = InL (mmapG pv fs u)
  mmapG pv fs (InR u) = InR (mmapG pv fs u)

instance (GMFunctor u fs vs, GMFunctor v fs vs) => GMFunctor (u :**: v) fs vs where
  mmapG pv fs (u :*: v) = mmapG pv fs u :*: mmapG pv fs v

instance GFMFunctor f fs vs => GMFunctor (UF f) fs vs where
  mmapG pv fs (InF f) = InF (mmapGF pv fs f)

class GFMFunctor (f :: Field *) (fs :: [*]) (vs :: [Variance]) where
  mmapGF :: Proxy vs -> HList fs -> InField f (Domains fs vs) -> InField f (Codomains fs vs)

instance GFMFunctor (FK a) fs vs where
  mmapGF _ fs (InK a) = InK a
  
instance (GFPMFunctor n fs vs,
          (fs :!: n) ~ (Domains fs vs :!: n -> Codomains fs vs :!: n)
         )
         => GFMFunctor (FP n) fs vs where
  mmapGF pv fs (InP a) = InP (mmapGFP (Proxy :: Proxy n) pv fs a)

class GFPMFunctor n fs vs where
  mmapGFP :: Proxy n -> Proxy vs -> HList fs -> fs :!: n
instance GFPMFunctor NZ ((a -> b) ': as) (v ': vs) where
  mmapGFP _ _ (HCons f _) a = f a
instance GFPMFunctor n as vs => GFPMFunctor (NS n) ((a -> b) ': as) (CoV ': vs) where
  mmapGFP _ _ (HCons _ fs) = mmapGFP (Proxy :: Proxy n) (Proxy :: Proxy vs) fs
instance GFPMFunctor n as vs => GFPMFunctor (NS n) ((a -> b) ': as) (ContraV ': vs) where
  mmapGFP _ _ (HCons _ fs) = mmapGFP (Proxy :: Proxy n) (Proxy :: Proxy vs) fs
  

type family ExpandFieldFunction (f :: [Field *]) (vfs :: [Variance]) (ps :: [*]) (vs :: [Variance]) :: [*] where
  ExpandFieldFunction '[]                '[]              ps vs = '[]
  ExpandFieldFunction (FK a ': fs)       (v ': vfs)       ps vs = (a -> a) ': ExpandFieldFunction fs vfs ps vs
  ExpandFieldFunction (FP n ': fs)       (CoV ': vfs)     ps vs = (ps :!: n) ': ExpandFieldFunction fs vfs ps vs
  ExpandFieldFunction (FP n ': fs)       (ContraV ': vfs) ps vs = (ps :!: n) ': ExpandFieldFunction fs vfs ps vs
  ExpandFieldFunction ((f :@: as) ': fs) (CoV ': vfs)     ps vs = (f :$: ExpandField as (Domains ps vs) -> f :$: ExpandField as (Codomains ps vs)) ': ExpandFieldFunction fs vfs ps vs
  ExpandFieldFunction ((f :@: as) ': fs) (ContraV ': vfs) ps vs = (f :$: ExpandField as (Codomains ps vs) -> f :$: ExpandField as (Domains ps vs)) ': ExpandFieldFunction fs vfs ps vs

class AdaptFieldFunction (f :: [Field *]) (vfs :: [Variance]) (ps :: [*]) (vs :: [Variance]) where
  adaptFieldFunction :: Proxy f -> Proxy vfs -> Proxy vs -> HList ps -> HList (ExpandFieldFunction f vfs ps vs)
  
instance AdaptFieldFunction '[] '[] ps vs where
  adaptFieldFunction _ _ _ fs = HNil
         
instance AdaptFieldFunction as vfs ps vs => AdaptFieldFunction (FK a ': as) (v ': vfs) ps vs where
  adaptFieldFunction _ _ pv ps = HCons id (adaptFieldFunction (Proxy :: Proxy as) (Proxy :: Proxy vfs) pv ps)

instance (GFPMFunctor n ps vs ,
          AdaptFieldFunction as vfs ps vs,
          (ps :!: n) ~ (Domains ps vs :!: n -> Codomains ps vs :!: n)
         )
         => AdaptFieldFunction (FP n ': as) (CoV ': vfs) ps vs where
  adaptFieldFunction _ _ pv ps =
    HCons
    (mmapGFP (Proxy :: Proxy n) pv ps)
    (adaptFieldFunction (Proxy :: Proxy as) (Proxy :: Proxy vfs) pv ps)

instance (GFPMFunctor n ps vs ,
          AdaptFieldFunction as vfs ps vs,
          Flip (ps :!: n) ~ (Domains ps vs :!: n -> Codomains ps vs :!: n)
         )
         => AdaptFieldFunction (FP n ': as) (ContraV ': vfs) ps vs where
  adaptFieldFunction _ _ pv ps =
    HCons
    (mmapGFP (Proxy :: Proxy n) pv ps)
    (adaptFieldFunction (Proxy :: Proxy as) (Proxy :: Proxy vfs) pv ps)

instance ( MFunctor f (ExpandFieldFunction bs vs' ps vs) vs',
           ExpandField bs (Codomains ps vs) ~ Codomains (ExpandFieldFunction bs vs' ps vs) vs',
           ExpandField bs (Domains ps vs) ~ Domains (ExpandFieldFunction bs vs' ps vs) vs',
           AdaptFieldFunction bs vs' ps vs,
           AdaptFieldFunction as vfs ps vs 
         )
         => AdaptFieldFunction ((f :@: bs) ': as) (CoV ': vfs) ps vs where
  adaptFieldFunction _ _ pv ps =
    HCons
    (mmapP (Proxy :: Proxy f) (Proxy :: Proxy vs') (adaptFieldFunction (Proxy :: Proxy bs) (Proxy :: Proxy vs') pv ps))
    (adaptFieldFunction (Proxy :: Proxy as) (Proxy :: Proxy vfs) pv ps)

type family FlipVariance vs where
  FlipVariance '[]             = '[]
  FlipVariance (CoV ': vs)     = ContraV ': FlipVariance vs
  FlipVariance (ContraV ': vs) = CoV ': FlipVariance vs

instance ( MFunctor f (ExpandFieldFunction bs (FlipVariance vs') ps vs) vs'
         , ExpandField bs (Domains ps vs) ~ Codomains (ExpandFieldFunction bs (FlipVariance vs') ps vs) vs'
         , ExpandField bs (Codomains ps vs) ~ Domains (ExpandFieldFunction bs (FlipVariance vs') ps vs) vs'
         , AdaptFieldFunction bs (FlipVariance vs') ps vs
         , AdaptFieldFunction as vfs ps vs 
         )
         => AdaptFieldFunction ((f :@: bs) ': as) (ContraV ': vfs) ps vs where
  adaptFieldFunction _ _ pv ps =
    HCons
    (mmapP (Proxy :: Proxy f) (Proxy :: Proxy vs') (adaptFieldFunction (Proxy :: Proxy bs) (Proxy :: Proxy (FlipVariance vs')) pv ps))
    (adaptFieldFunction (Proxy :: Proxy as) (Proxy :: Proxy vfs) pv ps)

instance (MFunctor f (ExpandFieldFunction as vs' ps vs) vs',
          ExpandField as (Codomains ps vs) ~ Codomains (ExpandFieldFunction as vs' ps vs) vs',
          ExpandField as (Domains ps vs) ~ Domains (ExpandFieldFunction as vs' ps vs) vs',
          AdaptFieldFunction as vs' ps vs
          )
         => GFMFunctor (f :@: as) ps vs where
  mmapGF _ ps (InA a) =
    InA (mmapP (Proxy :: Proxy f) (Proxy :: Proxy vs') (adaptFieldFunction (Proxy :: Proxy as) (Proxy :: Proxy vs') (Proxy :: Proxy vs) ps) (unsafeCoerce a))

