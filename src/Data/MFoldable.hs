{-# LANGUAGE DataKinds, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, PolyKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, DefaultSignatures, FlexibleContexts, InstanceSigs #-}

module Data.MFoldable where

import Data.MGeneric
import Data.MGeneric.Instances

import Data.HList
import Data.Proxy
import Data.Nat
import Unsafe.Coerce

type family MonoidMap as m where
  MonoidMap '[]       m = '[]
  MonoidMap (a ': as) m = (a -> m) ': MonoidMap as m
  
class MFoldable (f :: k) (as :: [*]) | as -> k where
  mfoldMap :: Monoid m => HList (MonoidMap as m) -> f :$: as -> m
  mfoldMap = mfoldMapP (Proxy :: Proxy f) (Proxy :: Proxy as)

  mfoldMapP :: Monoid m => Proxy f -> Proxy as -> HList (MonoidMap as m) -> f :$: as -> m
  default mfoldMapP :: (MGeneric (f :$: as), as ~ Pars (f :$: as),
                        GMFoldable (Rep (f :$: as)) as,
                        Monoid m
                       )
                       =>  Proxy f -> Proxy as -> HList (MonoidMap as m) -> f :$: as -> m
  mfoldMapP _ _ fs = mfoldMapG fs . from

class GMFoldable (f :: Un *) (as :: [*]) where
  mfoldMapG :: Monoid m => HList (MonoidMap as m) -> In f as -> m

instance GMFoldable UV fs where
  mfoldMapG _ _ = undefined

instance GMFoldable UT fs where
  mfoldMapG _ InT = mempty

instance (GMFoldable u as, GMFoldable v as) => GMFoldable (u :++: v) as where
  mfoldMapG fs (InL u) = mfoldMapG fs u
  mfoldMapG fs (InR v) = mfoldMapG fs v

instance (GMFoldable u as, GMFoldable v as) => GMFoldable (u :**: v) as where
  mfoldMapG fs (u :*: v) = mfoldMapG fs u `mappend` mfoldMapG fs v

instance GFMFoldable f as => GMFoldable (UF f) as where
  mfoldMapG fs (InF f) = mfoldMapGF fs f

class GFMFoldable (f :: Field *) (as :: [*]) where
  mfoldMapGF :: Monoid m => HList (MonoidMap as m) -> InField f as -> m

instance GFMFoldable (FK a) as where
  mfoldMapGF fs (InK _) = mempty
  
instance GFPMFoldable n as => GFMFoldable (FP n) as where
  mfoldMapGF fs (InP a) = mfoldMapGFP (Proxy :: Proxy n) (Proxy :: Proxy as) fs a

class GFPMFoldable n as where
  mfoldMapGFP :: Monoid m => Proxy n -> Proxy as -> HList (MonoidMap as m) -> as :!: n -> m

instance GFPMFoldable NZ ((a -> b) ': as) where
  mfoldMapGFP _ _ (HCons f _) a = f a
                         
instance GFPMFoldable n as => GFPMFoldable (NS n) ((a -> b) ': as) where
  mfoldMapGFP _ p (HCons _ fs) a = mfoldMapGFP (Proxy :: Proxy n) (Proxy :: Proxy as) fs a

class AdaptFieldMonoid (f :: [Field *]) (as :: [*]) where
  adaptFieldMonoid :: Monoid m => Proxy f -> Proxy as -> Proxy m -> HList (MonoidMap as m) -> HList (MonoidMap (ExpandField f as) m)
  
instance AdaptFieldMonoid '[] fs where
  adaptFieldMonoid _ _ _ fs = HNil
         
instance AdaptFieldMonoid as fs => AdaptFieldMonoid (FK a ': as) fs where
  adaptFieldMonoid _ pf pm fs = HCons (const mempty) (adaptFieldMonoid (Proxy :: Proxy as) pf pm fs)
 
instance (MFoldable f (ExpandField bs fs), AdaptFieldMonoid bs fs, AdaptFieldMonoid as fs)
         => AdaptFieldMonoid ((f :@: bs) ': as) fs where
  adaptFieldMonoid _ pf pm fs = HCons (mfoldMapP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandField bs fs)) (adaptFieldMonoid (Proxy :: Proxy bs) pf pm fs)) (adaptFieldMonoid (Proxy :: Proxy as) pf pm fs)

instance (MFoldable f (ExpandField as bs), AdaptFieldMonoid as bs)
         => GFMFoldable (f :@: as) bs where
  mfoldMapGF :: forall m. Monoid m => HList (MonoidMap bs m) -> InField (f :@: as) bs -> m
  mfoldMapGF fs (InA a) =
    mfoldMapP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandField as bs)) (adaptFieldMonoid (Proxy :: Proxy as) (Proxy :: Proxy bs) (Proxy :: Proxy m) fs) (unsafeCoerce a)
