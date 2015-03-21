{-# LANGUAGE KindSignatures, DataKinds, TypeOperators, TypeFamilies, PolyKinds #-}

module Data.Nat where

data Nat = NZ | NS Nat

type family (as :: [k]) :!: (n :: Nat) :: k where
  (a ': as) :!: NZ     = a
  (a ': as) :!: (NS n) = as :!: n

type family (as :: [[k]]) :!!: (n :: Nat) :: [k] where
  '[]       :!!: n = '[]
  (a ': as) :!!: n = (a :!: n) ': (as :!!: n)
    
