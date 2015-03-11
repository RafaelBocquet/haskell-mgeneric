{-# LANGUAGE DataKinds, TypeOperators, GADTs, MultiParamTypeClasses, PolyKinds, ScopedTypeVariables #-}

module Data.HList where

import Data.Nat
import Data.Proxy

data HList as where
  HNil  :: HList '[]
  HCons :: a -> HList as -> HList (a ': as)

infixr 6 `HCons`

class HNth as n where
  hnth :: HList as -> Proxy n -> as :!: n
  
instance HNth as n => HNth (b ': as) (NS n) where
  hnth (HCons _ as) _ = hnth as (Proxy :: Proxy n)

instance HNth (a ': as) NZ where
  hnth (HCons a _) _ = a
