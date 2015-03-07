{-# LANGUAGE DataKinds, TypeOperators, TemplateHaskell, TypeFamilies, ScopedTypeVariables #-}

module Data.MGeneric.Instances where

import Data.MGeneric
import Data.MGeneric.TH

import Data.Monoid
import Control.Applicative
import Control.Monad.Identity

deriveMGeneric ''[]
deriveMGeneric ''Maybe
deriveMGeneric ''Either
deriveMGeneric ''Bool
deriveMGeneric ''Ordering
deriveMGeneric ''()
deriveMGeneric ''(,)
deriveMGeneric ''(,,)
deriveMGeneric ''(,,,)
deriveMGeneric ''(,,,,)
deriveMGeneric ''(,,,,,)
deriveMGeneric ''(,,,,,,)
deriveMGeneric ''(,,,,,,,)
deriveMGeneric ''(,,,,,,,,)
deriveMGeneric ''Last
deriveMGeneric ''First
deriveMGeneric ''Product
deriveMGeneric ''Sum
deriveMGeneric ''Endo
deriveMGeneric ''Const
deriveMGeneric ''Identity
