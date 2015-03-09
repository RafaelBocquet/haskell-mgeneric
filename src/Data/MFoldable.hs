{-# LANGUAGE DataKinds, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, PolyKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, DefaultSignatures, FlexibleContexts, InstanceSigs #-}

module Data.MFoldable where

import Data.MGeneric

import Data.Unapply
import Data.HList
import Data.Proxy
import Data.Nat
import Unsafe.Coerce

-- FoldMap

type family MonoidMap as m where
  MonoidMap '[]       m = '[]
  MonoidMap (a ': as) m = (a -> m) ': MonoidMap as m
             
class MFoldMap (f :: k) (as :: [*]) | as -> k where
  mfoldMapP :: Monoid m => Proxy f -> Proxy as -> HList (MonoidMap as m) -> f :$: as -> m
  default mfoldMapP :: (MGeneric (f :$: as), as ~ Pars (f :$: as),
                        GMFoldMap (Rep (f :$: as)) as,
                        Monoid m
                       )
                       =>  Proxy f -> Proxy as -> HList (MonoidMap as m) -> f :$: as -> m
  mfoldMapP _ _ fs = mfoldMapG fs . from

mfoldMap :: forall m a f as.
            ( Monoid m,
              Unapply a f as,
              MFoldMap f as
            ) => HList (MonoidMap as m) -> a -> m
mfoldMap = mfoldMapP (Proxy :: Proxy f) (Proxy :: Proxy as)

-- Fold

class Repeat m as where
  repeatId :: Proxy m -> Proxy as -> HList (MonoidMap as m)
  
instance Repeat m '[] where
  repeatId _ _ = HNil

instance Repeat m as => Repeat m (m ': as) where
  repeatId pm _ = HCons id (repeatId pm (Proxy :: Proxy as))


mfold :: forall m f as a.
         ( Monoid m,
           Repeat m as,
           MFoldMap f as,
           Unapply a f as
         ) => a -> m
mfold = mfoldMap (repeatId (Proxy :: Proxy m) (Proxy :: Proxy as))

-- Generics

class GMFoldMap (f :: Un *) (as :: [*]) where
  mfoldMapG :: Monoid m => HList (MonoidMap as m) -> In f as -> m

instance GMFoldMap UV fs where
  mfoldMapG _ _ = undefined

instance GMFoldMap UT fs where
  mfoldMapG _ InT = mempty

instance (GMFoldMap u as, GMFoldMap v as) => GMFoldMap (u :++: v) as where
  mfoldMapG fs (InL u) = mfoldMapG fs u
  mfoldMapG fs (InR v) = mfoldMapG fs v

instance (GMFoldMap u as, GMFoldMap v as) => GMFoldMap (u :**: v) as where
  mfoldMapG fs (u :*: v) = mfoldMapG fs u `mappend` mfoldMapG fs v

instance GFMFoldMap f as => GMFoldMap (UF f) as where
  mfoldMapG fs (InF f) = mfoldMapGF fs f

class GFMFoldMap (f :: Field *) (as :: [*]) where
  mfoldMapGF :: Monoid m => HList (MonoidMap as m) -> InField f as -> m

instance GFMFoldMap (FK a) as where
  mfoldMapGF fs (InK _) = mempty
  
instance GFPMFoldMap n as => GFMFoldMap (FP n) as where
  mfoldMapGF fs (InP a) = mfoldMapGFP (Proxy :: Proxy n) (Proxy :: Proxy as) fs a

class GFPMFoldMap n as where
  mfoldMapGFP :: Monoid m => Proxy n -> Proxy as -> HList (MonoidMap as m) -> as :!: n -> m

instance GFPMFoldMap NZ (a ': as) where
  mfoldMapGFP _ _ (HCons f _) = f
                         
instance GFPMFoldMap n as => GFPMFoldMap (NS n) (a ': as) where
  mfoldMapGFP _ p (HCons _ fs) = mfoldMapGFP (Proxy :: Proxy n) (Proxy :: Proxy as) fs

class AdaptFieldMonoid (f :: [Field *]) (as :: [*]) where
  adaptFieldMonoid :: Monoid m => Proxy f -> Proxy as -> Proxy m -> HList (MonoidMap as m) -> HList (MonoidMap (ExpandField f as) m)
  
instance AdaptFieldMonoid '[] fs where
  adaptFieldMonoid _ _ _ fs = HNil
         
instance AdaptFieldMonoid as fs => AdaptFieldMonoid (FK a ': as) fs where
  adaptFieldMonoid _ pf pm fs = HCons (const mempty) (adaptFieldMonoid (Proxy :: Proxy as) pf pm fs)

instance (GFPMFoldMap n fs, AdaptFieldMonoid as fs) => AdaptFieldMonoid (FP n ': as) fs where
  adaptFieldMonoid _ pf pm fs = HCons (mfoldMapGFP (Proxy :: Proxy n) (Proxy :: Proxy fs) fs) (adaptFieldMonoid (Proxy :: Proxy as) pf pm fs)
                                                     
instance (MFoldMap f (ExpandField bs fs), AdaptFieldMonoid bs fs, AdaptFieldMonoid as fs)
         => AdaptFieldMonoid ((f :@: bs) ': as) fs where
  adaptFieldMonoid _ pf pm fs = HCons (mfoldMapP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandField bs fs)) (adaptFieldMonoid (Proxy :: Proxy bs) pf pm fs)) (adaptFieldMonoid (Proxy :: Proxy as) pf pm fs)

instance (MFoldMap f (ExpandField as bs), AdaptFieldMonoid as bs)
         => GFMFoldMap (f :@: as) bs where
  mfoldMapGF :: forall m. Monoid m => HList (MonoidMap bs m) -> InField (f :@: as) bs -> m
  mfoldMapGF fs (InA a) =
    mfoldMapP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandField as bs)) (adaptFieldMonoid (Proxy :: Proxy as) (Proxy :: Proxy bs) (Proxy :: Proxy m) fs) (unsafeCoerce a)
