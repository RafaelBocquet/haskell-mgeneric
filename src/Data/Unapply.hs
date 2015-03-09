{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies, TypeOperators, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

module Data.Unapply where

import Data.MGeneric
import Data.Monoid

class (f ~ (f' :$: as)) => Unapply (f :: *) (f' :: k') (as :: [*]) | f' as -> f, f -> f' as 

instance Unapply [a] [] '[a]
instance Unapply (Maybe a) Maybe '[a]
instance Unapply (Either a b) Either '[a, b]
instance Unapply Bool Bool '[]
instance Unapply Ordering Ordering '[]
instance Unapply () () '[]
instance Unapply (a,b) (,) '[a, b]
instance Unapply (a,b,c) (,,) '[a, b, c]
instance Unapply (a,b,c,d) (,,,) '[a, b, c, d]
instance Unapply (a,b,c,d,e) (,,,,) '[a, b, c, d, e] 
instance Unapply (a,b,c,d,e,f) (,,,,,) '[a, b, c, d, e, f]
instance Unapply (a,b,c,d,e,f,g) (,,,,,,) '[a, b, c, d, e, f, g]
instance Unapply (a,b,c,d,e,f,g,h) (,,,,,,,) '[a, b, c, d, e, f, g, h]
instance Unapply (a,b,c,d,e,f,g,h,i) (,,,,,,,,) '[a, b, c, d, e, f, g, h, i]
instance Unapply (Last a) Last '[a]
instance Unapply (First a) First '[a]
instance Unapply (Product a) Product '[a]
instance Unapply (Sum a) Sum '[a]
instance Unapply (a -> b) (->) '[a, b]
