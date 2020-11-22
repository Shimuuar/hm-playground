{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
-- |
-- AST and data type for simple 
module HM.Simple.AST where

import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import HM.Infer.Types
import HM.Recursion

----------------------------------------------------------------
-- Data types
----------------------------------------------------------------

-- | AST for language. @l@ is type of label which is used as labels
--   for pretty printer for bound variables. @a@ is type of free
--   variables
data Expr l a
  = Prim PrimOp                 -- ^ Primitive operation
  | Lam l (Expr l a)            -- ^ Lambda expression
  | Let l (Expr l a) (Expr l a) -- ^ Nonrecursive let binding
  | Ap  (Expr l a) (Expr l a)   -- ^ Function application
  | FV a                        -- ^ FreeVariable
  | BV l !Int                   -- ^ Bound variable
  | LitI Integer                -- ^ Literal
  deriving stock (Show, Eq, Functor, Foldable, Traversable)

-- | Primitive operations
data PrimOp
  = OpAdd
  | OpSub
  | OpMul
  | OpAnd
  | OpOr
  | OpNot
  deriving (Show, Eq)

-- | Type in monomorphic context
data Type a
  = TVar a
  | Type a :-> Type a
  | TInt
  | TBool
  deriving stock (Show, Eq, Functor, Foldable, Traversable)


$(makeBaseFunctor ''Expr)
$(makeBaseFunctor ''Type)

----------------------------------------------------------------
-- Instances
----------------------------------------------------------------

instance TypeLike Type Type where
  freeTypeVars = cata $ \case
    TVarF x  -> Set.singleton x
    a :->$ b -> a <> b
    TIntF    -> mempty
    TBoolF   -> mempty
  applySubst (Subst m) = replaceCata $ \case
    TVarF x -> x `Map.lookup` m
    _       -> Nothing
