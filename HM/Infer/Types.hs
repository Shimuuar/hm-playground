{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}
-- |
-- Data types which are used for type inference for all languages
module HM.Infer.Types where

import Data.Map (Map)
import Data.Set (Set, (\\))
import qualified Data.Map.Strict as Map

----------------------------------------------------------------
-- Type classes and general data types
----------------------------------------------------------------

-- | Monad which provides supply of fresh names for type variables
class Monad m => MonadHM a m | m -> a where
  freshTyVar :: m a 

-- | Type class for data types of programming language.
class TypeLike f t | f -> t where
  -- | Set of free type variables of given type
  freeTypeVars :: Ord a => f a -> Set a
  -- | Apply substitution of type variables
  applySubst   :: Ord a => Subst t a -> f a -> f a

-- -- | Types that support unification
-- class Unify f e where
--   unify :: (Ord a) => f a -> f a -> Either e (Subst f a)

----------------------------------------------------------------
-- Data types
----------------------------------------------------------------

-- | Substitution for type variables 
newtype Subst f a = Subst (Map a (f a))
  deriving (Show)

instance (TypeLike f f, Ord a) => Semigroup (Subst f a) where
  Subst s1 <> Subst s2 = Subst $ (applySubst (Subst s1) <$> s2) <> s1

instance (TypeLike f f, Ord a) => Monoid (Subst f a) where
  mempty = Subst mempty


-- | Polymorphic data type (called type scheme in original paper)
data PolyT f a = PolyT (Set a) (f a)
  deriving Show

instance TypeLike f t => TypeLike (PolyT f) t where
  freeTypeVars (PolyT bound ty) = freeTypeVars ty \\ bound
  applySubst (Subst m) (PolyT bound ty)
    = PolyT bound
    $ applySubst (Subst (m `Map.withoutKeys` bound)) ty
