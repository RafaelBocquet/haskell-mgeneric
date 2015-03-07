{-# LANGUAGE LambdaCase, ViewPatterns, TemplateHaskell, TypeOperators, DataKinds #-}

module Data.MGeneric.TH where

import Data.Nat
import Data.MGeneric

import Control.Lens hiding (index)
import Control.Applicative

import Data.Foldable
import Data.Traversable

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Lens

import Unsafe.Coerce

import Data.Function

viewData :: Dec -> Maybe (Cxt, Name, [TyVarBndr], [Con], [Name])
viewData (DataD a b c d e)    = Just (a, b, c, d, e)
viewData (NewtypeD a b c d e) = Just (a, b, c, [d], e)
viewData _                    = Nothing

viewCon :: Con -> (Name, [Type])
viewCon (NormalC n tys)   = (n, fmap snd tys)
viewCon (RecC n tys)      = (n, fmap (view _3) tys)
viewCon (InfixC a n b)    = (n, [snd a, snd b])
viewCon (ForallC _ _ con) = viewCon con

index :: Eq a => [a] -> a -> Maybe Int
index []       x = Nothing
index (a : as) x
  | x == a    = Just 0
  | otherwise = index as x <&> succ

nthNat :: Int -> TypeQ
nthNat n | n < 0 = fail "..."
nthNat 0 = conT 'NZ
nthNat n = appT (conT 'NS) (nthNat (n-1))

viewAppType :: Type -> (Type, [Type])
viewAppType (ForallT _ _ a)                   = viewAppType a
viewAppType (AppT (viewAppType -> (a, as)) b) = (a, as ++ [b])
viewAppType (SigT a _)                        = viewAppType a
viewAppType ListT                             = (ConT ''[], [])
viewAppType a                                 = (a, [])

typeEncoding :: [Name] -> Type -> Name
typeEncoding ps (viewAppType -> (VarT a, [])) = case index ps a of
  Nothing -> 'InK
  Just n  -> 'InP
typeEncoding ps (viewAppType -> (ConT a, [])) = 'InK
typeEncoding ps (viewAppType -> (ConT a, as)) = 'InA
-- typeEncoding ps (viewAppType -> (a, as)) = fail (show (a, as))


encodeField :: [Name] -> Type -> TypeQ
encodeField ps (viewAppType -> (VarT a, [])) = case index ps a of
  Nothing -> (appT (conT 'FK) (varT a))
  Just n  -> (appT (conT 'FP) (nthNat n))
encodeField ps (viewAppType -> (ConT a, [])) =
  appT (conT 'FK) (conT a)
encodeField ps (viewAppType -> (ConT a, as)) =
  appT
   (appT (conT '(:@:)) (conT a))
   (foldr (\a -> appT (appT (conT '(:)) a)) (conT '[]) (encodeField ps <$> as))
encodeField ps (viewAppType -> (a, as)) = fail (show (a, as))


deriveMGeneric :: Name -> Q [Dec]
deriveMGeneric n = do
  reify n >>= \case
    TyConI (viewData -> Just (cxt, nm, fmap (view name) -> tvs, fmap viewCon -> cons, _)) -> do
      let ty = foldl appT (conT nm) (varT <$> tvs)
          rep  = tySynInstD
                 ''Rep
                 (tySynEqn [ty]
                  $ foldr ?? (conT 'UV) ?? (fmap snd cons)
                  $ \con ->
                           appT
                            (appT
                             (conT '(:++:))
                             (foldr (\a -> appT (appT (conT '(:**:)) a)) (conT 'UT) (appT (conT 'UF) . encodeField tvs <$> con))
                            )
                 )
          pars = tySynInstD
                 ''Pars
                 (tySynEqn [ty]
                  (foldr (appT . appT (conT '(:))) (conT '[]) (varT <$> tvs))
                 )
          from = funD 'Data.MGeneric.from
                  $ zip cons (iterate (appE (conE 'InR) .) (appE (conE 'InL)))
                  <&> \((nm, tys), scon) -> do
                    vs <- forM tys $ \ty -> newName "x" <&> \x -> (x, typeEncoding tvs ty)
                    clause [conP nm (varP . fst <$> vs)] ?? []
                     $ normalB
                     $ scon
                     $ foldr (\a -> appE (appE (conE '(:*:)) a)) (conE 'InT) (vs <&> \(v, n) -> appE (conE 'InF) (appE (conE n) (varE v)))
          to   = funD 'Data.MGeneric.to
                  $ zip cons (iterate (\p q -> conP 'InR [p q]) (\p -> conP 'InL [p]))
                  <&> \((nm, tys), spat) -> do
                    vs <- forM tys $ \ty -> newName "x" <&> \x -> (x, typeEncoding tvs ty)
                    let vsp = foldr (\a b -> conP '(:*:) [a, b]) (conP 'InT []) (vs <&> \(v, n) -> conP 'InF [conP n [varP v]])
                    clause [spat vsp] ?? []
                     $ normalB
                     $ foldl appE (conE nm) (appE (varE 'unsafeCoerce) . varE . fst <$> vs)
      mgenInst <- instanceD
                  (return [])
                  (appT (conT ''MGeneric) ty)
                  [rep, pars, from, to]
      return [mgenInst]
    _ ->
      fail "TODO"
