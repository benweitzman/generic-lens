{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Internal.Lens
-- Copyright   :  (C) 2017 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Internal lens helpers. Only exported for Haddock
--
-----------------------------------------------------------------------------
module Data.Generics.Internal.Lens where

import Data.Functor.Identity
import Control.Applicative  ( Const (..) )
import Data.Profunctor      ( Choice(..), dimap, Profunctor(..) )
import GHC.Generics         ( (:*:) (..), Generic (..), M1 (..), Rep, (:+:) (..) )



data Tagged a b = Tagged { unTagged :: b }

instance Profunctor Tagged where
    dimap _ r (Tagged x) = Tagged $ r x

instance Choice Tagged where
    left' (Tagged x) = Tagged $ Left x
    right' (Tagged x) = Tagged $ Right x

-- | Type alias for lens
type Lens' s a
  = forall f. Functor f => (a -> f a) -> s -> f s

type Prism' s a
  = forall p f. (Choice p, Applicative f) => p a (f a) -> p s (f s)

-- | Build a 'Control.Lens.Prism.Prism'.
--
-- @'Either' t a@ is used instead of @'Maybe' a@ to permit the types of @s@ and @t@ to differ.
--
prism :: (a -> s) -> (s -> Either s a) -> Prism' s a
prism bt seta = dimap seta (either pure (fmap bt)) . right'
{-# INLINE prism #-}

-- | This is usually used to build a 'Prism'', when you have to use an operation like
-- 'Data.Typeable.cast' which already returns a 'Maybe'.
prism' :: (a -> s) -> (s -> Maybe a) -> Prism' s a
prism' bs sma = prism bs (\s -> maybe (Left s) Right (sma s))
--{-# INLINE prism' #-}

type AReview t b = Tagged b (Identity b) -> Tagged t (Identity t)

review :: AReview t b -> b -> t
review r = runIdentity . unTagged . r . Tagged . Identity

-- | Getting
(^.) :: s -> ((a -> Const a a) -> s -> Const a s) -> a
s ^. l = getConst (l Const s)
infixl 8 ^.

-- | Setting
set :: ((a -> Identity b) -> s -> Identity t) -> b -> s -> t
set l b
  = runIdentity . l (\_ -> Identity b)

-- | Lens focusing on the first element of a product
first :: Lens' ((a :*: b) x) (a x)
first f (a :*: b)
  = fmap (:*: b) (f a)

-- | Lens focusing on the second element of a product
second :: Lens' ((a :*: b) x) (b x)
second f (a :*: b)
  = fmap (a :*:) (f b)

combine :: Lens' (s x) a -> Lens' (t x) a -> Lens' ((:+:) s t x) a
combine sa _ f (L1 s) = fmap (\a -> L1 (set sa a s)) (f (s ^. sa))
combine _ ta f (R1 t) = fmap (\a -> R1 (set ta a t)) (f (t ^. ta))

-- | A type and its generic representation are isomorphic
repIso :: Generic a => Lens' a (Rep a x)
repIso a = fmap to . a . from

-- | 'M1' is just a wrapper around `f p`
lensM :: Lens' (M1 i c f p) (f p)
lensM f (M1 x) = fmap M1 (f x)

-- | 'M1' is just a wrapper around `f p`
prismM :: Prism' (M1 i c f p) (f p)
prismM x = dimap (\(M1 a) -> a) (fmap M1) x

repIso' :: Generic a => Prism' a (Rep a x)
repIso' = prism' to (Just . from)
