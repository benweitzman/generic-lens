{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Generics.Sum.HasConstructor where

import Data.Profunctor
import Data.Generics.Internal.Lens
import Data.Kind
import GHC.Generics
import GHC.TypeLits

{-
class ToTuple f where
    type AsTuple f :: Type

    toTuple :: Rep f x -> AsTuple f

instance ToTuple (S1 b (Rec0 a)) where
-}

class AsTuple (f :: Type -> Type) where
    type ToTuple f :: Type

    toTuple :: f x -> ToTuple f
    fromTuple :: ToTuple f -> f x

    tuplePrism :: Prism' (f x) (ToTuple f)
    tuplePrism = prism' fromTuple (Just . toTuple)


instance AsTuple (S1 m (Rec0 a)) where
    type ToTuple (S1 _ (Rec0 a)) = a

    toTuple (M1 (K1 a)) = a
    fromTuple a = (M1 (K1 a))

instance (AsTuple l, AsTuple r) => AsTuple (l :*: r) where
    type ToTuple (l :*: r) = (ToTuple l, ToTuple r)

    toTuple (l :*: r) = (toTuple l, toTuple r)
    fromTuple (l, r) = (fromTuple l :*: fromTuple r)



{-
type family ToTuple f where
    ToTuple (S1 _ (Rec0 a)) = a
-}

type family Build (constructor :: Symbol) f :: Maybe (Type -> Type) where
    Build c (C1 ('MetaCons c _ _) a) = 'Just a
    Build c (C1 _ _) = 'Nothing
    Build c (D1 _ f) = Build c f
    Build c (f :+: g) = Build c f <|> Build c g

class HasConstructor (constructor :: Symbol) a s  where
    constructor :: Prism' s a

instance
  ( Generic s
  , Build constructor (Rep s) ~ 'Just a -- this is needed for the fundep for some reason
  , GHasConstructor constructor (Rep s) a
  , q ~ ToTuple a
  , AsTuple a
  ) => HasConstructor constructor q s where
    constructor = repIso' . gconstructor @constructor . tuplePrism


class GHasConstructorSum (constructor :: Symbol) f g a w  | constructor f g -> a where
    sumConstructor :: Prism' ((f :+: g) x) (a x)

instance GHasConstructor constructor f a => GHasConstructorSum constructor f g a ('Just a) where
    sumConstructor = prism' (\a -> L1 a) (\x -> case x of L1 a -> Just a; _ -> Nothing) . gconstructor @constructor

instance GHasConstructor constructor g a => GHasConstructorSum constructor f g a 'Nothing where
    sumConstructor = prism' (\a -> R1 a) (\x -> case x of R1 a -> Just a; _ -> Nothing) . gconstructor @constructor

class GHasConstructor (constructor :: Symbol) s a | s constructor -> a where
    gconstructor :: Prism' (s t) (a t)


instance GHasConstructor constructor (M1 C ('MetaCons constructor p f) s) s where
    gconstructor = prism (\a -> M1 a) (\(M1 a) -> Right a)


instance GHasConstructor constructor s a => GHasConstructor constructor (M1 D c s) a where
    gconstructor = prismM . gconstructor @constructor

instance (GHasConstructorSum constructor f g a (Build constructor f)) => GHasConstructor constructor (f :+: g) a where
    gconstructor = sumConstructor @constructor @_ @_ @_ @(Build constructor f)

{-
instance (GHasConstructor constructor s a) => GHasConstructor constructor (s' :+: s) a where
    gconstructor = prism' (\a -> R1 a) (\x -> case x of R1 a -> Just a; _ -> Nothing) . gconstructor @constructor
-}


type family (a :: Maybe k) <|> (b :: Maybe k) :: Maybe k where
  'Just x <|> _  = 'Just x
  _ <|> b = b
