{-# LANGUAGE KindSignatures, DataKinds, TypeOperators, TypeFamilies #-}

module Data.Nat where

data Nat = NZ | NS Nat

type family (as :: [*]) :!: (n :: Nat) :: * where
  (a ': as) :!: NZ     = a
  (a ': as) :!: (NS n) = as :!: n
