{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
-- |
-- Helpers and extra utils for recursion schemes
module HM.Recursion where

import Data.Functor.Foldable

----------------------------------------------------------------
-- Annotations for recursive data type
----------------------------------------------------------------

-- | Attaches annotations for every constructor of data type @a@
data Ann x a = Ann x (Base a (Ann x a))

-- | Functor type for 'Ann' data type
data AnnF x a r = AnnF x (Base a r)


deriving instance Functor     (Base a) => Functor     (AnnF x a)
deriving instance Foldable    (Base a) => Foldable    (AnnF x a)
deriving instance Traversable (Base a) => Traversable (AnnF x a)


type instance Base (Ann x a) = AnnF x a

instance Recursive a => Recursive (Ann x a) where
  project (Ann x a) = AnnF x a
instance Corecursive a => Corecursive (Ann x a) where
  embed (AnnF x a) = Ann x a

deriving instance (Show x, Show (Base a (Ann x a))) => Show (Ann x a)
deriving instance (Show x, Show (Base a r))         => Show (AnnF x a r)


----------------------------------------------------------------
-- Extra morphisms
----------------------------------------------------------------

-- | Catamorphism variant that carries parameter around
rcata :: Recursive t
      => (e -> Base t (e -> a) -> a)
      -> (e -> t -> a)
rcata f = go
  where
    go e = f e . fmap (flip go) . project

-- | Descend into data type and replace nodes that match predicate function
replaceCata
  :: (Recursive t, Corecursive t)
  => (Base t t -> Maybe t)
  -> t -> t
replaceCata fun = cata $ \x ->
  case fun x of Nothing -> embed x
                Just x' -> x'
