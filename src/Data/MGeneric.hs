{-# LANGUAGE RankNTypes, GADTs, KindSignatures, DataKinds, TypeOperators, TypeFamilies, PolyKinds, UndecidableInstances #-}

module Data.MGeneric where

import Data.Nat

type family (f :: k) :$: (as :: [*]) :: * where
  f :$: '[]       = f
  f :$: (a ': as) = f a :$: as

-- Blah 

data Un s = UV
          | UT
          | UF (Field s)
          | Un s :**: Un s
          | Un s :++: Un s

data Field s = FK s
             | FP Nat
             | forall k. k :@: [Field s]

data In (u :: Un *) (ps :: [*]) :: * where
  InT :: In UT ps
  InF :: InField f ps -> In (UF f) ps
  InL :: In u ps -> In (u :++: v) ps
  InR :: In v ps -> In (u :++: v) ps
  (:*:) :: In u ps -> In v ps -> In (u :**: v) ps

infixr 5 :*:

data InField (f :: Field *) (ps :: [*]) :: * where
  InK :: a -> InField (FK a) ps
  InP :: ps :!: n -> InField (FP n) ps
  InA :: f :$: ExpandField as ps -> InField (f :@: as) ps

type family ExpandField (f :: [Field *]) (ps :: [*]) :: [*] where
  ExpandField '[]                ps = '[]
  ExpandField (FK a ': fs)       ps = a ': ExpandField fs ps
  ExpandField (FP n ': fs)       ps = (ps :!: n) ': ExpandField fs ps
  ExpandField ((f :@: as) ': fs) ps = (f :$: ExpandField as ps) ': ExpandField fs ps

class MGeneric (a :: *) where
  type Rep a  :: Un *
  type Pars a :: [*]
  from :: a -> In (Rep a) (Pars a)
  to   :: In (Rep a) (Pars a) -> a
