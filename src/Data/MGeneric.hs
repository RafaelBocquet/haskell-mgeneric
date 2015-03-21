{-# LANGUAGE RankNTypes, GADTs, KindSignatures, DataKinds, TypeOperators, TypeFamilies, PolyKinds, UndecidableInstances #-}

module Data.MGeneric
       ( (:$:)
       , Un(..)
       , Field(..)
       , In(..)
       , InField(..)
       , ExpandField
       , ExpandFields
       , MGeneric(..)
       )
       where

import Data.Nat

-- | Type level application
-- 
-- > f :$: '[a, b, ...] ~ f a b ...
type family (f :: k) :$: (as :: [*]) :: * where
  f :$: '[]       = f
  f :$: (a ': as) = f a :$: as

-- | Universe kind
--
-- The s parameter should always be *
data Un s = UV             -- ^ Empty universe
          | UT             -- ^ Trivial universe
          | UF (Field s)   -- ^ Lifts from the field universe
          | Un s :**: Un s -- ^ Product universe
          | Un s :++: Un s -- ^ Sum universe

-- | Field kind
--
-- The s parameter should always be *
--
-- (FK a) can be replaced by (a :@: []), but the empty application case is often handled differently in generic type classes
data Field s = FK s                      -- ^ Constant field
             | FP Nat                    -- ^ Parameter field
             | forall k. k :@: [Field s] -- ^ Application field

-- | Universe `u` inhabitation with parameters `ps`
data In (u :: Un *) (ps :: [*]) :: * where
  InT :: In UT ps
  InF :: InField f ps -> In (UF f) ps
  InL :: In u ps -> In (u :++: v) ps
  InR :: In v ps -> In (u :++: v) ps
  (:*:) :: In u ps -> In v ps -> In (u :**: v) ps

infixr 5 :*:

-- | Field `f` inhabitation with parameters `ps`
data InField (f :: Field *) (ps :: [*]) :: * where
  InK :: a -> InField (FK a) ps
  InP :: ps :!: n -> InField (FP n) ps
  InA :: f :$: ExpandFields as ps -> InField (f :@: as) ps

type family ExpandField (f :: Field *) (ps :: [*]) :: * where
  ExpandField (FK a)       ps = a
  ExpandField (FP n)       ps = ps :!: n
  ExpandField (f :@: as)   ps = f :$: ExpandFields as ps

type family ExpandFields (f :: [Field *]) (ps :: [*]) :: [*] where
  ExpandFields '[]                ps = '[]
  ExpandFields (FK a ': fs)       ps = a ': ExpandFields fs ps
  ExpandFields (FP n ': fs)       ps = (ps :!: n) ': ExpandFields fs ps
  ExpandFields ((f :@: as) ': fs) ps = (f :$: ExpandFields as ps) ': ExpandFields fs ps

-- | Representable types with parameters
class MGeneric (a :: *) where
  -- | Representation of a
  type Rep a  :: Un *
  -- | Parameters of a
  type Pars a :: [*]
  -- | Convert from the datatype to its representation
  from :: a -> In (Rep a) (Pars a)
  -- | Convert to the datatype from its representation
  to   :: In (Rep a) (Pars a) -> a
