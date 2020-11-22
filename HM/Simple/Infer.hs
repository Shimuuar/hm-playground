{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
-- |
module HM.Simple.Infer where

import Control.Monad.Except
import Data.Foldable
import Data.Functor.Foldable
import Data.Map (Map)
import Data.Set ((\\))
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import HM.Simple.AST
import HM.Infer.Types

----------------------------------------------------------------
-- Typing helpers
----------------------------------------------------------------

-- | Typing environment
data TypeEnv a = TypeEnv
  { freeVarsTy  :: (Map a (PolyT Type a)) -- ^ Types of free variable of expression
  , boundVarsTy :: [PolyT Type a]         -- ^ Types of bound variables of expression
  }
  deriving Show

instance TypeLike TypeEnv Type where
  freeTypeVars TypeEnv{..} = foldMap freeTypeVars freeVarsTy
                          <> foldMap freeTypeVars boundVarsTy
  applySubst s TypeEnv{..} = TypeEnv
    { freeVarsTy  = applySubst s <$> freeVarsTy
    , boundVarsTy = applySubst s <$> boundVarsTy
    }

instantiate :: (MonadHM a m, Ord a) => PolyT Type a -> m (Type a)
instantiate (PolyT bound ty) = do
  subst <- Subst . Map.fromList <$> mapM (\x -> (,TVar x) <$> freshTyVar) (toList bound)
  pure $ applySubst subst ty

generalize :: Ord a => TypeEnv a -> Type a -> PolyT Type a
generalize env ty = PolyT (freeTypeVars ty \\ freeTypeVars env) ty


----------------------------------------------------------------
-- Hindley-Milner algorithm-W
----------------------------------------------------------------

-- Type unification. This function produces substitution which either
-- unifies two types or fails to do so.
unify
  :: (Ord a, MonadHM a m, MonadError String m)
  => Type a -> Type a -> m (Subst Type a)
unify (TVar x) t = bindTyVar x t
unify t (TVar x) = bindTyVar x t
unify (a :-> b) (a' :-> b') = do sA <- unify a a'
                                 sB <- unify (applySubst sA b) (applySubst sA b')
                                 -- FIXME: Is <> commutative here?
                                 pure $ sA <> sB
unify TInt  TInt  = pure mempty
unify TBool TBool = pure mempty
unify _     _     = throwError $ "Unification failed"

bindTyVar
  :: (MonadError String m, MonadHM a m, Ord a)
  => a -> Type a -> m (Subst Type a)
bindTyVar x ty
  | TVar x == ty       = pure mempty
  | x `Set.member` ftv = throwError "Occurs check fails"
  | otherwise          = pure $ Subst $ Map.singleton x ty
  where
    ftv = freeTypeVars ty


-- Single step of type inference algorithm
inferStep
  :: (MonadHM a m, MonadError String m, Ord a, Show a)
  => TypeEnv a
  -> Base (Expr l a) (TypeEnv a -> m (Subst Type a, Type a))
  -> m (Subst Type a, Type a)
inferStep env = \case
  -- Variables
  FVF   x -> case x `Map.lookup` freeVarsTy env of
    Nothing -> throwError $  "Unbound free var " ++ show x
    Just ty -> do t <- instantiate ty
                  pure (mempty, t)
  BVF _ i -> case atI i $ boundVarsTy env of
    Nothing -> throwError "Internal error: no type for bound variable"
    Just ty -> do t <- instantiate ty
                  pure (mempty, t)
  -- Lambda abstraction
  LamF _ e     -> do
    x <- freshTyVar
    let env' = bindVarType (PolyT mempty (TVar x)) env
    (s1,t1) <- e env'
    pure (s1, applySubst s1 (TVar x) :-> t1)
  -- Nonrecursive let
  LetF _ e1 e2 -> do
    (s1,t1) <- e1 env
    let ty   = generalize env t1
        env' = bindVarType ty env
    (s2,t2) <- e2 env'
    pure (s1 <> s2, t2)
  --
  ApF f a -> do
    (s1,t1) <- f env
    (s2,t2) <- a (applySubst s1 env)
    -- FIXME: ???
    x  <- freshTyVar
    s3 <- unify (applySubst s2 t1) (t2 :-> TVar x)
    return (s3 <> s2 <> s1, applySubst s3 (TVar x))
  --
  PrimF op -> pure (mempty, primopType op)
  LitIF{}  -> pure (mempty, TInt)
  where
    atI 0 (x:_)  = Just x
    atI i (_:xs) = atI (i - 1) xs
    atI _ []     = Nothing
    --
    bindVarType ty TypeEnv{..} = TypeEnv { boundVarsTy = ty : boundVarsTy
                                         , ..
                                         }

primopType :: PrimOp -> Type a
primopType = \case
  OpAdd -> TInt  :-> (TInt  :-> TInt)
  OpSub -> TInt  :-> (TInt  :-> TInt)
  OpMul -> TInt  :-> (TInt  :-> TInt)
  OpAnd -> TBool :-> (TBool :-> TBool)
  OpOr  -> TBool :-> (TBool :-> TBool)
  OpNot -> TBool :-> TBool
