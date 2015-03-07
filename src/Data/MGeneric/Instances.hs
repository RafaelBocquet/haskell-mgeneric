{-# LANGUAGE DataKinds, TypeOperators, TemplateHaskell, TypeFamilies, ScopedTypeVariables #-}

module Data.MGeneric.Instances where

import Data.MGeneric
import Data.MGeneric.TH

deriveMGeneric ''[]
deriveMGeneric ''Maybe
deriveMGeneric ''Bool
