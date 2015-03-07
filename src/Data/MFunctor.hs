{-# LANGUAGE DataKinds, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, PolyKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, DefaultSignatures, FlexibleContexts #-}

module Data.MFunctor where

import Data.MGeneric
import Data.MGeneric.Instances

import Data.HList
import Data.Proxy
import Data.Nat
import Unsafe.Coerce

type family Domains fs where
  Domains '[]              = '[]
  Domains ((a -> b) ': as) = a ': Domains as
  
type family Codomains fs where
  Codomains '[]              = '[]
  Codomains ((a -> b) ': as) = b ': Codomains as

class MFunctor (f :: k) (fs :: [*]) | fs -> k where
  mmap :: HList fs -> f :$: Domains fs -> f :$: Codomains fs
  mmap = mmapP (Proxy :: Proxy f)

  mmapP :: Proxy f -> HList fs -> f :$: Domains fs -> f :$: Codomains fs
  default mmapP :: (MGeneric (f :$: Domains fs), MGeneric (f :$: Codomains fs),
                    Rep (f :$: Domains fs) ~ Rep (f :$: Codomains fs),
                    Domains fs ~ Pars (f :$: Domains fs),
                    Codomains fs ~ Pars (f :$: Codomains fs),
                    GMFunctor (Rep (f :$: Domains fs)) fs
                   )
                   => Proxy f -> HList fs -> f :$: Domains fs -> f :$: Codomains fs
  mmapP _ fs = to . mmapG fs . from

class GMFunctor (f :: Un *) (fs :: [*]) where
  mmapG :: HList fs -> In f (Domains fs) -> In f (Codomains fs)

instance GMFunctor UV fs where
  mmapG _ _ = undefined

instance GMFunctor UT fs where
  mmapG _ InT = InT

instance (GMFunctor u fs, GMFunctor v fs) => GMFunctor (u :++: v) fs where
  mmapG fs (InL u) = InL (mmapG fs u)
  mmapG fs (InR u) = InR (mmapG fs u)

instance (GMFunctor u fs, GMFunctor v fs) => GMFunctor (u :**: v) fs where
  mmapG fs (u :*: v) = mmapG fs u :*: mmapG fs v

instance GFMFunctor f fs => GMFunctor (UF f) fs where
  mmapG fs (InF f) = InF (mmapGF fs f)

class GFMFunctor (f :: Field *) (fs :: [*]) where
  mmapGF :: HList fs -> InField f (Domains fs) -> InField f (Codomains fs)

instance GFMFunctor (FK a) fs where
  mmapGF fs (InK a) = InK a
  
instance GFPMFunctor n fs => GFMFunctor (FP n) fs where
  mmapGF fs (InP a) = InP (mmapGFP (Proxy :: Proxy n) fs a)

class GFPMFunctor n fs where
  mmapGFP :: Proxy n -> HList fs -> Domains fs :!: n -> Codomains fs :!: n

instance GFPMFunctor NZ ((a -> b) ': as) where
  mmapGFP _ (HCons f _) a = f a
                         
instance GFPMFunctor n as => GFPMFunctor (NS n) ((a -> b) ': as) where
  mmapGFP _ (HCons _ fs) a = mmapGFP (Proxy :: Proxy n) fs a

type family ExpandFieldFunction (f :: [Field *]) (ps :: [*]) :: [*] where
  ExpandFieldFunction '[]          ps       = '[]
  ExpandFieldFunction (FK a ': fs) ps       = (a -> a) ': ExpandFieldFunction fs ps
  ExpandFieldFunction (FP n ': fs) ps       = (ps :!: n) ': ExpandFieldFunction fs ps
  ExpandFieldFunction ((f :@: as) ': fs) ps = (f :$: ExpandField as (Domains ps) -> f :$: ExpandField as (Codomains ps)) ': ExpandFieldFunction fs ps

class AdaptFieldFunction (f :: [Field *]) (fs :: [*]) where
  adaptFieldFunction :: Proxy f -> HList fs -> HList (ExpandFieldFunction f fs)
  
instance AdaptFieldFunction '[] fs where
  adaptFieldFunction _ fs = HNil
         
instance AdaptFieldFunction as fs => AdaptFieldFunction (FK a ': as) fs where
  adaptFieldFunction _ fs = HCons id (adaptFieldFunction (Proxy :: Proxy as) fs)
                                                         
instance (GFPMFunctor n fs,
          AdaptFieldFunction as fs,
          (fs :!: n) ~ (Domains fs :!: n -> Codomains fs :!: n)
         )
         => AdaptFieldFunction (FP n ': as) fs where
  adaptFieldFunction _ fs = HCons (mmapGFP (Proxy :: Proxy n) fs) (adaptFieldFunction (Proxy :: Proxy as) fs)

instance (MFunctor f (ExpandFieldFunction bs fs),
          (f :$: ExpandField bs (Codomains fs)) ~ (f :$: Codomains (ExpandFieldFunction bs fs)),
          (f :$: ExpandField bs (Domains fs)) ~ (f :$: Domains (ExpandFieldFunction bs fs)),
          AdaptFieldFunction bs fs,
          AdaptFieldFunction as fs
         )
         => AdaptFieldFunction ((f :@: bs) ': as) fs where
  adaptFieldFunction _ fs = HCons (mmapP (Proxy :: Proxy f) (adaptFieldFunction (Proxy :: Proxy bs) fs)) (adaptFieldFunction (Proxy :: Proxy as) fs)

instance (MFunctor f (ExpandFieldFunction as fs),
          (f :$: ExpandField as (Codomains fs)) ~ (f :$: Codomains (ExpandFieldFunction as fs)),
          (f :$: ExpandField as (Domains fs)) ~ (f :$: Domains (ExpandFieldFunction as fs)),
          AdaptFieldFunction as fs
          )
         => GFMFunctor (f :@: as) fs where
  mmapGF fs (InA a) =
    InA (mmapP (Proxy :: Proxy f) (adaptFieldFunction (Proxy :: Proxy as) fs) (unsafeCoerce a))

