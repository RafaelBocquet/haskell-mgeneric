{-# LANGUAGE DataKinds, TypeOperators, GADTs, MultiParamTypeClasses, PolyKinds, ScopedTypeVariables, TypeFamilies, RankNTypes, FlexibleInstances #-}

module Data.HList where

import Data.Nat
import Data.Proxy

data HList as where
  HNil  :: HList '[]
  HCons :: a -> HList as -> HList (a ': as)

infixr 6 `HCons`

class HNth as n where
  hnth :: HList as -> Proxy n -> as :!: n
  
instance HNth as n => HNth (b ': as) ('NS n) where
  hnth (HCons _ as) _ = hnth as (Proxy :: Proxy n)

instance HNth (a ': as) 'NZ where
  hnth (HCons a _) _ = a

type family Map f as where
  Map f '[] = '[]
  Map f (a ': as) = f a ': Map f as

class HMap (as :: [k]) (f :: k -> *) (g :: k -> *) where
  hmap :: Proxy as -> (forall (i :: k). f i -> g i) -> HList (Map f as) -> HList (Map g as)
instance HMap '[] f g where
  hmap _ _ HNil = HNil
instance HMap as f g => HMap (a ': as) f g where
  hmap _ f (HCons a as) = HCons (f a) (hmap (Proxy :: Proxy as) f as)

class HLookup n as where
  hlookup :: Proxy n -> Proxy as -> HList as -> as :!: n
instance HLookup NZ (a ': as) where
  hlookup _ _ (HCons f _) = f
instance HLookup n as => HLookup (NS n) (a ': as) where
  hlookup _ _ (HCons _ fs) = hlookup (Proxy :: Proxy n) (Proxy :: Proxy as) fs
