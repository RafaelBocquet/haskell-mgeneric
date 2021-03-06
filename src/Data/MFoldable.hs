{-# LANGUAGE DataKinds, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, PolyKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, DefaultSignatures, FlexibleContexts, InstanceSigs #-}
{-# OPTIONS_HADDOCK prune #-}

module Data.MFoldable where

import Data.MGeneric

import Data.Unapply
import Data.HList
import Data.Proxy
import Data.Nat
import Unsafe.Coerce

import Data.Monoid

-- | > MonoidMap as m ~ Map (\a -> (a -> m)) as
type family MonoidMap as m where
  MonoidMap '[]       m = '[]
  MonoidMap (a ': as) m = (a -> m) ': MonoidMap as m

-- | `MFoldable` type class, generalisation of `Data.Foldable.Foldable`, `Data.Bifoldable.Bifoldable`, etc.
--
-- >>> instance MFoldable (,,) '[a, b, c]
-- >>> mfoldMap (Sum `HCons` (Sum . length) `HCons` const mempty `HCons` HNil) (1, "foobar", 5) = 7
class MFoldable (f :: k) (as :: [*]) | as -> k where
  -- | see `mfoldMap`
  mfoldMapP :: Monoid m => Proxy f -> Proxy as -> HList (MonoidMap as m) -> f :$: as -> m
  default mfoldMapP :: (MGeneric (f :$: as), as ~ Pars (f :$: as),
                        GMFoldable (Rep (f :$: as)) as,
                        Monoid m
                       )
                       =>  Proxy f -> Proxy as -> HList (MonoidMap as m) -> f :$: as -> m
  mfoldMapP _ _ fs = mfoldMapG fs . from


-- | Map elements of each parameter type of a structure to a monoid, and combine the results.
--
-- Proxy-less version of `mfoldMapP`
--
-- > mfoldMap :: HList '[a1 -> m, ..., an -> m] -> f :$: '[a1, ..., an] -> m
mfoldMap :: forall m a f as.
            ( Monoid m,
              Unapply a f as,
              MFoldable f as
            ) => HList (MonoidMap as m) -> a -> m
mfoldMap = mfoldMapP (Proxy :: Proxy f) (Proxy :: Proxy as)

class Repeat m as where
  repeatId :: Proxy m -> Proxy as -> HList (MonoidMap as m)
instance Repeat m '[] where
  repeatId _ _ = HNil
instance Repeat m as => Repeat m (m ': as) where
  repeatId pm _ = HCons id (repeatId pm (Proxy :: Proxy as))

-- | Combine the elements of a structure when all its parameters are the same monoid.
mfold :: forall m f as a.
         ( Monoid m,
           Repeat m as,
           MFoldable f as,
           Unapply a f as
         ) => a -> m
mfold = mfoldMap (repeatId (Proxy :: Proxy m) (Proxy :: Proxy as))

-- Generics

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

instance GFPMFoldable NZ (a ': as) where
  mfoldMapGFP _ _ (HCons f _) = f
                         
instance GFPMFoldable n as => GFPMFoldable (NS n) (a ': as) where
  mfoldMapGFP _ p (HCons _ fs) = mfoldMapGFP (Proxy :: Proxy n) (Proxy :: Proxy as) fs

class AdaptFieldMonoid (f :: [Field *]) (as :: [*]) where
  adaptFieldMonoid :: Monoid m => Proxy f -> Proxy as -> Proxy m -> HList (MonoidMap as m) -> HList (MonoidMap (ExpandFields f as) m)
  
instance AdaptFieldMonoid '[] fs where
  adaptFieldMonoid _ _ _ fs = HNil
         
instance AdaptFieldMonoid as fs => AdaptFieldMonoid (FK a ': as) fs where
  adaptFieldMonoid _ pf pm fs = HCons (const mempty) (adaptFieldMonoid (Proxy :: Proxy as) pf pm fs)

instance (GFPMFoldable n fs, AdaptFieldMonoid as fs) => AdaptFieldMonoid (FP n ': as) fs where
  adaptFieldMonoid _ pf pm fs = HCons (mfoldMapGFP (Proxy :: Proxy n) (Proxy :: Proxy fs) fs) (adaptFieldMonoid (Proxy :: Proxy as) pf pm fs)
                                                     
instance (MFoldable f (ExpandFields bs fs), AdaptFieldMonoid bs fs, AdaptFieldMonoid as fs)
         => AdaptFieldMonoid ((f :@: bs) ': as) fs where
  adaptFieldMonoid _ pf pm fs = HCons (mfoldMapP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandFields bs fs)) (adaptFieldMonoid (Proxy :: Proxy bs) pf pm fs)) (adaptFieldMonoid (Proxy :: Proxy as) pf pm fs)

instance (MFoldable f (ExpandFields as bs), AdaptFieldMonoid as bs)
         => GFMFoldable (f :@: as) bs where
  mfoldMapGF :: forall m. Monoid m => HList (MonoidMap bs m) -> InField (f :@: as) bs -> m
  mfoldMapGF fs (InA a) =
    mfoldMapP (Proxy :: Proxy f) (Proxy :: Proxy (ExpandFields as bs)) (adaptFieldMonoid (Proxy :: Proxy as) (Proxy :: Proxy bs) (Proxy :: Proxy m) fs) (unsafeCoerce a)
