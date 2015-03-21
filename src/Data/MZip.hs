{-# LANGUAGE DataKinds, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, PolyKinds, TypeFamilies, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, DefaultSignatures, FlexibleContexts #-}
{-# OPTIONS_HADDOCK prune #-}

module Data.MZip where

import Data.MGeneric
import Data.Unapply

import Data.HList
import Data.Proxy
import Data.Nat
import Unsafe.Coerce

import Control.Applicative

type family Dom (f :: *) where
  Dom (a -> b) = a
type family Codom (f :: *) where
  Codom (a -> b) = b
type family Doms (fs :: [*]) :: [*] where
  Doms '[]              = '[]
  Doms ((a -> b) ': as) = a ': Doms as
type family Codoms (fs :: [*]) :: [*] where
  Codoms '[]              = '[]
  Codoms ((a -> b) ': as) = b ': Codoms as

type family LCodoms (n :: Nat) (fs :: [*]) where
  LCodoms NZ     fs = fs
  LCodoms (NS n) fs = LCodoms n (Codoms fs)

type family ZipInput n f where
  ZipInput NZ     a        = Maybe a
  ZipInput (NS n) (a -> b) = a -> ZipInput n b

type family ZipInputs n fs where
  ZipInputs n '[]       = '[]
  ZipInputs n (f ': fs) = ZipInput n f ': ZipInputs n fs

type family ZipWithType' (n :: Nat) (f :: k) (fs :: [*]) :: * where
  ZipWithType' NZ     f fs = (f :$: fs)
  ZipWithType' (NS n) f fs = f :$: (Doms fs) -> ZipWithType' n f (Codoms fs)

type family ZipWithType (n :: Nat) (f :: k) (fs :: [*]) :: * where
  ZipWithType NZ     f fs = Maybe (f :$: fs)
  ZipWithType (NS n) f fs = f :$: (Doms fs) -> ZipWithType n f (Codoms fs)

type family ZipWithTypeUn (n :: Nat) (f :: Un *) (fs :: [*]) :: * where
  ZipWithTypeUn NZ     f fs = Maybe (In f fs)
  ZipWithTypeUn (NS n) f fs = In f (Doms fs) -> ZipWithTypeUn n f (Codoms fs)

type family ZipWithTypeField (n :: Nat) (f :: Field *) (fs :: [*]) :: * where
  ZipWithTypeField NZ     f fs = Maybe (InField f fs)
  ZipWithTypeField (NS n) f fs = InField f (Doms fs) -> ZipWithTypeField n f (Codoms fs)  

class MZipWithG n f rf fs where
  mzipWithPG :: Proxy n -> Proxy f -> Proxy rf -> Proxy fs -> ZipWithTypeUn n rf fs -> ZipWithType n f fs
instance ( fs ~ Pars (f :$: fs)
         , rf ~ Rep (f :$: fs)
         , MGeneric (f :$: fs)
         ) => MZipWithG NZ f rf fs where
  mzipWithPG _ _ _ _ a = fmap to a
instance ( MZipWithG n f rf (Codoms fs)
         , rf ~ Rep (f :$: Doms fs)
         , Doms fs ~ Pars (f :$: Doms fs)
         , MGeneric (f :$: Doms fs)
         ) => MZipWithG (NS n) f rf fs where
  mzipWithPG _ pf prf _ a b = mzipWithPG (Proxy :: Proxy n) pf prf (Proxy :: Proxy (Codoms fs)) (a (from b))

-- |
class MZipWith (n :: Nat) (f :: k) (fs :: [*]) where
  -- |
  mzipWithP :: Proxy n -> Proxy f -> Proxy fs -> HList (ZipInputs n fs) -> ZipWithType n f fs
  default mzipWithP :: ( rf ~ Rep (f :$: LCodoms n fs)
                       , MZipWithG n f rf fs
                       , GMZipWith n rf fs
                       ) => Proxy n -> Proxy f -> Proxy fs -> HList (ZipInputs n fs) -> ZipWithType n f fs
  mzipWithP pn pf pfs fs = mzipWithPG pn pf prf (Proxy :: Proxy fs) (mzipWithG pn prf pfs fs)
    where prf = Proxy :: Proxy (Rep (f :$: LCodoms n fs))


class (ZipInput n f ~ a) => ZipInputC n f a | n f -> a, a -> f
instance ZipInputC NZ a (Maybe a)
instance ZipInputC n b c => ZipInputC (NS n) (a -> b) (a -> c)

class (ZipInputs n fs ~ a) => ZipInputsC n fs a | n fs -> a, a -> fs
instance ZipInputsC n '[] '[]
instance (ZipInputC n f c, ZipInputsC n fs b) => ZipInputsC n (f ': fs) (c ': b)

class (ZipWithType n f fs ~ a) => ZipWithTypeC n f fs a | n f fs -> a, a -> n f fs
instance Unapply a f fs => ZipWithTypeC NZ f fs (Maybe a)
instance (Unapply a f (Doms fs), ZipWithTypeC n f (Codoms fs) b) => ZipWithTypeC (NS n) f fs (a -> b)

-- | `mzipWith` zips n structures together if they have the same shape, or fails (with `Nothing`) if the shapes do not match.
--
-- > mzipWith :: HList '[a11 -> ... -> an1 -> b1, ...] -> f a11 ... a1m -> f an1 ... anm -> f b1 ... bm
mzipWith :: forall n f fs b.
            ( MZipWith n f fs
            , MakeZipInputs n fs
            , ZipWithTypeC n f fs b
            , ZipInputsC n fs (ZipInputs n fs)
            ) => HList fs -> b
mzipWith fs = mzipWithP (Proxy :: Proxy n) (Proxy :: Proxy f) (Proxy :: Proxy fs) (makeZipInputs (Proxy :: Proxy n) fs)

class MakeZipInput n f where
  makeZipInput :: Proxy n -> f -> ZipInput n f
instance MakeZipInput NZ a where
  makeZipInput _ = Just
instance MakeZipInput n b => MakeZipInput (NS n) (a -> b) where
  makeZipInput _ f a = makeZipInput (Proxy :: Proxy n) (f a)

class MakeZipInputs n fs where
  makeZipInputs :: ZipInputsC n fs a => Proxy n -> HList fs -> HList a
instance MakeZipInputs n '[] where
  makeZipInputs _ _ = HNil
instance ( MakeZipInput n f
         , MakeZipInputs n fs
         , ZipInputsC n fs (ZipInputs n fs)
         ) => MakeZipInputs n (f ': fs) where
  makeZipInputs pn (HCons f fs) = HCons (makeZipInput pn f) (makeZipInputs pn fs)

class GMZipWith (n :: Nat) (f :: Un *) (fs :: [*]) where
  mzipWithG :: Proxy n -> Proxy f -> Proxy fs -> HList (ZipInputs n fs) -> ZipWithTypeUn n f fs

instance GMZipWith n UV fs where
  mzipWithG _ _ _ = undefined

class GMTZipWith n fs where
  mzipWithGT :: Proxy n -> Proxy fs -> ZipWithTypeUn n UT fs
instance GMTZipWith NZ fs where
  mzipWithGT _ _ = Just InT
instance GMTZipWith n (Codoms fs) => GMTZipWith (NS n) fs where
  mzipWithGT _ pf _ = mzipWithGT (Proxy :: Proxy n) (Proxy :: Proxy (Codoms fs))
instance GMTZipWith n fs => GMZipWith n UT fs where
  mzipWithG _ _ _ _ = mzipWithGT (Proxy :: Proxy n) (Proxy :: Proxy fs)

class GMZipWithFail n u fs where
  mzipWithFail :: Proxy n -> Proxy u -> Proxy fs -> ZipWithTypeUn n u fs
instance GMZipWithFail NZ u fs where
  mzipWithFail _ _ _ = Nothing

class GMLZipWith n u v fs where
  mzipWithGL :: Proxy n -> Proxy u -> Proxy v -> Proxy fs -> ZipWithTypeUn n u fs -> ZipWithTypeUn n (u :++: v) fs
instance GMLZipWith NZ u v fs where
  mzipWithGL _ _ _ _ u = fmap InL u
instance ( GMLZipWith n u v (Codoms fs)
         , GMZipWithFail n (u :++: v) (Codoms fs)
         ) => GMLZipWith (NS n) u v fs where
  mzipWithGL _ pu pv _ f (InL u) = mzipWithGL (Proxy :: Proxy n) pu pv (Proxy :: Proxy (Codoms fs)) (f u)
  mzipWithGL _ pu pv _ f (InR _) = mzipWithFail (Proxy :: Proxy n) (Proxy :: Proxy (u :++: v)) (Proxy :: Proxy (Codoms fs))
class GMRZipWith n u v fs where
  mzipWithGR :: Proxy n -> Proxy u -> Proxy v -> Proxy fs -> ZipWithTypeUn n v fs -> ZipWithTypeUn n (u :++: v) fs
instance GMRZipWith NZ u v fs where
  mzipWithGR _ _ _ _ v = fmap InR v
instance ( GMRZipWith n u v (Codoms fs)
         , GMZipWithFail n (u :++: v) (Codoms fs)
         ) => GMRZipWith (NS n) u v fs where
  mzipWithGR _ pu pv _ f (InR v) = mzipWithGR (Proxy :: Proxy n) pu pv (Proxy :: Proxy (Codoms fs)) (f v)
  mzipWithGR _ pu pv _ f (InL _) = mzipWithFail (Proxy :: Proxy n) (Proxy :: Proxy (u :++: v)) (Proxy :: Proxy (Codoms fs))
instance ( GMZipWith (NS n) u fs, GMZipWith (NS n) v fs
         , GMLZipWith n u v (Codoms fs), GMRZipWith n u v (Codoms fs)
         ) => GMZipWith (NS n) (u :++: v) fs where
  mzipWithG _ _ pf fs (InL u) = mzipWithGL (Proxy :: Proxy n) (Proxy :: Proxy u) (Proxy :: Proxy v) (Proxy :: Proxy (Codoms fs)) (mzipWithG (Proxy :: Proxy (NS n)) (Proxy :: Proxy u) pf fs u)
  mzipWithG _ _ pf fs (InR v) = mzipWithGR (Proxy :: Proxy n) (Proxy :: Proxy u) (Proxy :: Proxy v) (Proxy :: Proxy (Codoms fs)) (mzipWithG (Proxy :: Proxy (NS n)) (Proxy :: Proxy v) pf fs v)

class GPiMZipWith n u v fs where
  mzipWithGPi :: Proxy n -> Proxy u -> Proxy v -> Proxy fs -> ZipWithTypeUn n u fs -> ZipWithTypeUn n v fs -> ZipWithTypeUn n (u :**: v) fs
instance GPiMZipWith NZ u v fs where
  mzipWithGPi _ _ _ _ f g = (:*:) <$> f <*> g
instance GPiMZipWith n u v (Codoms fs) => GPiMZipWith (NS n) u v fs where
  mzipWithGPi _ _ _ _ f g (u :*: v) = mzipWithGPi (Proxy :: Proxy n) (Proxy :: Proxy u) (Proxy :: Proxy v) (Proxy :: Proxy (Codoms fs)) (f u) (g v)
instance (GMZipWith n u fs, GMZipWith n v fs, GPiMZipWith n u v fs) => GMZipWith n (u :**: v) fs where
  mzipWithG pn _ pf fs = mzipWithGPi pn (Proxy :: Proxy u) (Proxy :: Proxy v) pf (mzipWithG pn (Proxy :: Proxy u) pf fs) (mzipWithG pn (Proxy :: Proxy v) pf fs)

class GMZipWithF n f fs where
  mzipWithGFF :: Proxy n -> Proxy f -> Proxy fs -> ZipWithTypeField n f fs -> ZipWithTypeUn n (UF f) fs
instance GMZipWithF NZ f fs where
  mzipWithGFF _ _ _ f = fmap InF f
instance GMZipWithF n f (Codoms fs) => GMZipWithF (NS n) f fs where
  mzipWithGFF _ pf _ f (InF b) = mzipWithGFF (Proxy:: Proxy n) pf (Proxy :: Proxy (Codoms fs)) (f b)
instance (GFMZipWith n f fs, GMZipWithF n f fs) => GMZipWith n (UF f) fs where
  mzipWithG pn _ pf fs = mzipWithGFF pn (Proxy :: Proxy f) pf (mzipWithGF pn (Proxy :: Proxy f) pf fs)

class GFMZipWith (n :: Nat) (f :: Field *) (fs :: [*]) where
  mzipWithGF :: Proxy n -> Proxy f -> Proxy fs -> HList (ZipInputs n fs) -> ZipWithTypeField n f fs

-- instance GFMZipWith n (FK a) fs where
--   mzipWithGF _ fs (InK a) = InK a

class GFPMZipWith n m fs where
  mzipWithGFP :: Proxy n -> Proxy m -> Proxy fs -> (ZipInputs n fs :!: m) -> ZipWithTypeField n (FP m) fs
instance (Maybe (fs :!: m) ~ (ZipInputs NZ fs :!: m)) => GFPMZipWith NZ m fs where
  mzipWithGFP _ _ _ a = fmap InP a
instance ( (ZipInputs (NS n) fs :!: m) ~ (Doms fs :!: m -> ZipInputs n (Codoms fs) :!: m)
         , GFPMZipWith n m (Codoms fs)
         ) => GFPMZipWith (NS n) m fs where
  mzipWithGFP _ _ _ f (InP a) = mzipWithGFP (Proxy :: Proxy n) (Proxy :: Proxy m) (Proxy :: Proxy (Codoms fs)) (f a)
instance (GFPMZipWith n m fs, HLookup m (ZipInputs n fs)) => GFMZipWith n (FP m) fs where
  mzipWithGF pn _ pf fs = mzipWithGFP (Proxy :: Proxy n) (Proxy :: Proxy m) pf (hlookup (Proxy :: Proxy m) (Proxy :: Proxy (ZipInputs n fs)) fs)

-- type family NId n a where
--   NId NZ     a = a
--   NId (NS n) a = a -> NId n a

type family ExpandFieldFunction (n :: Nat) (f :: [Field *]) (ps :: [*]) :: [*] where
  ExpandFieldFunction n '[]                ps = '[]
--ExpandFieldFunction n (FK a ': fs)       ps = NId n a ': ExpandFieldFunction fs vfs ps vs
  ExpandFieldFunction n (FP m ': fs)       ps = (ps :!: m) ': ExpandFieldFunction n fs ps
  ExpandFieldFunction n ((f :@: as) ': fs) ps = ZipWithType' n f (ExpandFieldFunction n as ps) ': ExpandFieldFunction n fs ps

class AdaptFieldFunction (n :: Nat) (f :: [Field *]) (ps :: [*]) where
  adaptFieldFunction :: Proxy n -> Proxy f -> Proxy ps -> HList (ZipInputs n ps) -> HList (ZipInputs n (ExpandFieldFunction n f ps))
  
instance AdaptFieldFunction n '[] ps where
  adaptFieldFunction _ _ _ fs = HNil

instance ( HLookup m (ZipInputs n ps)
         , ZipInput n (ps :!: m) ~ (ZipInputs n ps :!: m)
         , AdaptFieldFunction n as ps
         ) => AdaptFieldFunction n (FP m ': as) ps where
  adaptFieldFunction _ _ pf fs =
    HCons
    (hlookup (Proxy :: Proxy m) (Proxy :: Proxy (ZipInputs n ps)) fs)
    (adaptFieldFunction (Proxy :: Proxy n) (Proxy :: Proxy as) pf fs)

instance ( MZipWith n f (ExpandFieldFunction n bs ps)
         , ZipInput n (ZipWithType' n f (ExpandFieldFunction n bs ps)) ~ ZipWithType n f (ExpandFieldFunction n bs ps)
         , AdaptFieldFunction n bs ps
         , AdaptFieldFunction n as ps
         ) => AdaptFieldFunction n ((f :@: bs) ': as) ps where
  adaptFieldFunction pn _ pfs fs =
    HCons
    (mzipWithP pn pf (Proxy :: Proxy (ExpandFieldFunction n bs ps)) (adaptFieldFunction pn pb pfs fs))
    (adaptFieldFunction pn (Proxy :: Proxy as) pfs fs)
    where pf = Proxy :: Proxy f
          pb = Proxy :: Proxy bs

class GFAMZipWith n f as fs where
  mzipWithGFA :: Proxy n -> Proxy f -> Proxy as -> Proxy fs -> ZipWithType n f (ExpandFieldFunction n as fs) -> ZipWithTypeField n (f :@: as) fs
instance (ExpandFields as fs ~ ExpandFieldFunction NZ as fs)
         => GFAMZipWith NZ f as fs where
  mzipWithGFA _ _ _ _ (Just a) = Just (InA a)
  mzipWithGFA _ _ _ _ Nothing  = Nothing
instance ( ExpandFieldFunction n as (Codoms fs) ~ Codoms (ExpandFieldFunction (NS n) as fs)
         , Doms (ExpandFieldFunction (NS n) as fs) ~ ExpandFields as (Doms fs)
         , GFAMZipWith n f as (Codoms fs)
         ) => GFAMZipWith (NS n) f as fs where
  mzipWithGFA _ pf pa _ a (InA b) = mzipWithGFA (Proxy :: Proxy n) pf pa (Proxy :: Proxy (Codoms fs)) (a (unsafeCoerce b))
instance ( GFAMZipWith n f as fs
         , MZipWith n f (ExpandFieldFunction n as fs)
         , AdaptFieldFunction n as fs
         ) => GFMZipWith n (f :@: as) fs where
  mzipWithGF pn _ pfs fs = mzipWithGFA pn pf pa pfs (mzipWithP pn pf (Proxy :: Proxy (ExpandFieldFunction n as fs))  (adaptFieldFunction pn pa pfs fs))
    where pf  = Proxy :: Proxy f
          pa  = Proxy :: Proxy as

