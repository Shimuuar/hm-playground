{-# LANGUAGE ApplicativeDo              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MonadComprehensions        #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE RecursiveDo                #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
-- |
module Parser where

import Debug.Trace
import Control.Applicative
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Char
import Data.Foldable
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.List (elemIndex)
import Data.Map (Map)
import Data.Set (Set,(\\))
import Text.Earley
import Text.Regex.Applicative
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set

----------------------------------------------------------------
-- Recursion schemes stuff
----------------------------------------------------------------

data Ann  x a   = Ann  x (Base a (Ann x a))
data AnnF x a r = AnnF x (Base a r)

deriving instance Functor (Base a) => Functor (AnnF x a)

type instance Base (Ann x a) = AnnF x a

instance Recursive a => Recursive (Ann x a) where
  project (Ann x a) = AnnF x a
instance Corecursive a => Corecursive (Ann x a) where
  embed (AnnF x a) = Ann x a


----------------------------------------------------------------
-- AST & Parser
----------------------------------------------------------------

data PrimOp
  = OpAdd
  | OpSub
  | OpMul
  | OpAnd
  | OpOr
  | OpNot
  deriving (Show)

data E l a
  = Prim PrimOp
  | Lam l (E l a)
  | Let l (E l a) (E l a)
  | Ap  (E l a) (E l a)
  | FV a
  | BV l !Int
  | LitI Integer
  deriving Show

-- | Type in monomorphic context
data MonoT a
  = TVar a
  | MonoT a :-> MonoT a
  | TInt
  | TBool
  deriving (Show,Eq)

-- | Polymorphic type with 
data PolyT a = PolyT (Set a) (MonoT a)
  deriving Show

$(makeBaseFunctor ''E)
$(makeBaseFunctor ''MonoT)

----------------------------------------------------------------
-- Lexer
----------------------------------------------------------------

data Token
  = LParen          -- ^ @(@
  | RParen          -- ^ @)@
  | TokInt Integer  -- ^ Integer literal
  | TokIdent String -- ^ Identifier
  | TokAdd          -- ^ @+@
  | TokSub          -- ^ @-@
  | TokMul          -- ^ @*@
  | TokAnd          -- ^ @&&@
  | TokOr           -- ^ @||@
  | TokEq           -- ^ @=@
  | TokArr          -- ^ @->@
  | TokLam          -- ^ @\@
  | TokLet          -- ^ @let@
  | TokIn           -- ^ @in@
  deriving (Show, Eq)

tokenize :: String -> Maybe [Token]
tokenize = go
  where
    go []                = Just []
    go (c:s) | isSpace c = go s
    go s = do (tok,s') <- findLongestPrefix tokenRE s
              toks     <- go s'
              pure $ tok : toks
               

tokenRE :: RE Char Token
tokenRE
  =  LParen <$ "("
 <|> RParen <$ ")"
 <|> TokArr <$ "->"
 <|> TokAdd <$ "+"
 <|> TokSub <$ "-"
 <|> TokMul <$ "*"
 <|> TokLam <$ "\\"
 <|> TokEq  <$ "="
 <|> TokAnd <$ "&&"
 <|> TokOr  <$ "||"

 <|> TokIdent <$> ((<>) <$> "let" <*> some (psym isAlphaNum))
 <|> TokLet   <$ "let"
 <|> TokIdent <$> ((<>) <$> "in" <*> some (psym isAlphaNum))
 <|> TokIn    <$ "in"
 
 <|> TokInt . read <$> some (psym isDigit)
 <|> TokIdent <$> ((:) <$> psym isLetter <*> many (psym isAlphaNum))


----------------------------------------------------------------
-- Parser
----------------------------------------------------------------

grammar :: Grammar r (Prod r e Token (E String String))
grammar = mdo
  expr   <- rule $  pure Lam <* token TokLam <*> ident <* token TokArr <*> expr
                <|> pure Let <* token TokLet <*> ident <* token TokEq  <*> expr <* token TokIn <*> expr
                <|> exprP1
  exprP1 <- rule $  prim2 OpOr  <$> exprP1 <* token TokOr  <*> exprP2
                <|> exprP2
  exprP2 <- rule $  prim2 OpAnd <$> exprP2 <* token TokAnd <*> exprP3
                <|> exprP3
  exprP3 <- rule $  prim2 OpAdd <$> exprP3 <* token TokAdd <*> exprP4
                <|> prim2 OpAdd <$> exprP3 <* token TokSub <*> exprP4
                <|> exprP4
  exprP4 <- rule $  prim2 OpMul <$> exprP4 <* token TokMul <*> exprAp
                <|> exprAp
  exprAp <- rule $  Ap <$> exprAp <*> val
                <|> val
  val    <- rule $  terminal value
                <|> token LParen *> expr <* token RParen 
  return expr
  where
    ident = terminal $ \case
      TokIdent x -> Just x
      _          -> Nothing
    
    value (TokIdent x) = Just $ FV x
    value (TokInt   i) = Just $ LitI i
    value _            = Nothing

    prim2 op a b = Ap (Ap (Prim op) a) b

bindVariables :: Eq a => E a a -> E a a
bindVariables = go []
  where
    go env expr = case expr of
      Lam l e   -> Lam l $ go (l:env) e
      Let l e b -> Let l (go env e) (go (l:env) b)
      Ap  a b   -> Ap (go env a) (go env b)
      FV  x     -> case elemIndex x env of
        Just i  -> BV x i
        Nothing -> expr
      BV{}      -> error "We shouldn't have bound variables at this moment"
      Prim{}    -> expr
      LitI{}    -> expr

parse :: String -> E String String
parse s =
  case tokenize s of
    Nothing   -> error "Tokenization failed"
    Just toks -> case fullParses (parser grammar) toks of
      ([],e)  -> error $ "No parse: " ++ show (e :: Report String [Token])
      ([x],_) -> bindVariables x
      (_,e)   -> error $ "Multiple parses: " ++ show e


----------------------------------------------------------------
-- Pretty-printer
----------------------------------------------------------------

class Pretty a where
  pretty :: a -> String

instance Pretty [Char] where
  pretty = id

instance (Pretty l, Pretty a) => Pretty (E l a) where
  pretty = \case
    Prim op -> case op of
      OpAdd -> "(+)"
      OpSub -> "(-)"
      OpMul -> "(*)"
      OpAnd -> "(&&)"
      OpOr  -> "(||)"
      OpNot -> "not"
    Lam x e   -> "\\" <> pretty x <> " -> (" <> pretty e <> ")"
    Let x e b -> "let " <> pretty x <> "=" <> pretty e <> " in " <> pretty b
    Ap  f a   -> "("<>pretty f<>") ("<>pretty a<>")"
    FV  a     -> pretty a
    BV  l i   -> pretty l <> "@" <> show i
    LitI i    -> show i


----------------------------------------------------------------
-- Type checker
----------------------------------------------------------------

newtype InferM a = InferM (StateT Int (Either String) a)
  deriving newtype ( Functor,Applicative,Monad
                   , MonadError String
                   )

runInferM :: InferM a -> Either String a
runInferM (InferM m) = evalStateT m 0

instance MonadHM [Char] InferM where
  freshTyVar = InferM $ do i <- get
                           put $! i + 1
                           pure $ "a" ++ show i


class MonadError String m => MonadHM a m | m -> a where
  freshTyVar :: m a 

class TypeLike f where
  freeTypeVars :: Ord a => f a -> Set a
  applySubst   :: Ord a => Subst a -> f a -> f a

instance TypeLike MonoT where
  freeTypeVars = cata $ \case
    TVarF x  -> Set.singleton x
    a :->$ b -> a <> b
    TIntF    -> mempty
    TBoolF   -> mempty
  applySubst (Subst m) = replaceCata $ \case
    TVarF x -> x `Map.lookup` m
    _       -> Nothing

instance TypeLike PolyT where
  freeTypeVars (PolyT bound ty) = freeTypeVars ty \\ bound
  applySubst (Subst m) (PolyT bound ty)
    = PolyT bound
    $ applySubst (Subst (m `Map.withoutKeys` bound)) ty

-- | Substitute type variables by its value
newtype Subst a = Subst (Map a (MonoT a))
  deriving (Show)

instance Ord a => Semigroup (Subst a) where
  Subst s1 <> Subst s2 = Subst $ (applySubst (Subst s1) <$> s2) <> s1

instance Ord a => Monoid (Subst a) where
  mempty = Subst mempty
  
-- | Typing environment
data TypeEnv a = TypeEnv
  { freeVarsTy  :: (Map a (PolyT a)) -- ^ Types of free variable of expression
  , boundVarsTy :: [PolyT a]        -- ^ Types of bound variables of expression
  }
  deriving Show

instance TypeLike TypeEnv where
  freeTypeVars TypeEnv{..} = foldMap freeTypeVars freeVarsTy
                          <> foldMap freeTypeVars boundVarsTy
  applySubst s TypeEnv{..} = TypeEnv
    { freeVarsTy  = applySubst s <$> freeVarsTy
    , boundVarsTy = applySubst s <$> boundVarsTy
    }

instantiate :: (MonadHM a m, Ord a) => PolyT a -> m (MonoT a)
instantiate (PolyT bound ty) = do
  subst <- Subst . Map.fromList <$> mapM (\x -> (,TVar x) <$> freshTyVar) (toList bound)
  pure $ applySubst subst ty

generalize :: Ord a => TypeEnv a -> MonoT a -> PolyT a
generalize env ty = PolyT (freeTypeVars ty \\ freeTypeVars env) ty
  

unify :: (Ord a, MonadHM a m) => MonoT a -> MonoT a -> m (Subst a)
unify (TVar x) t = bindTyVar x t
unify t (TVar x) = bindTyVar x t
unify (a :-> b) (a' :-> b') = do sA <- unify a a'
                                 sB <- unify (applySubst sA b) (applySubst sA b')
                                 -- FIXME: Is <> commutative here?
                                 pure $ sA <> sB
unify TInt  TInt  = pure mempty
unify TBool TBool = pure mempty
unify _     _     = throwError $ "Unification failed"

bindTyVar :: (MonadHM a m, Ord a) => a -> MonoT a -> m (Subst a)
bindTyVar x ty
  | TVar x == ty       = pure mempty
  | x `Set.member` ftv = throwError "Occurs check fails"
  | otherwise          = pure $ Subst $ Map.singleton x ty
  where
    ftv = freeTypeVars ty

inferStep
  :: (MonadHM a m, Ord a, Show a)
  => TypeEnv a
  -> Base (E l a) (TypeEnv a -> m (Subst a, MonoT a))
  -> m (Subst a, MonoT a)
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
    traceShowM env'
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

infer
  :: (MonadHM a m, Ord a, Show a)
  => Map a (PolyT a) -> E l a -> m (Subst a, MonoT a)
infer freeEnv e = rcata inferStep (TypeEnv freeEnv []) e

primopType :: PrimOp -> MonoT a
primopType = \case
  OpAdd -> TInt  :-> (TInt  :-> TInt)
  OpSub -> TInt  :-> (TInt  :-> TInt)
  OpMul -> TInt  :-> (TInt  :-> TInt)
  OpAnd -> TBool :-> (TBool :-> TBool)
  OpOr  -> TBool :-> (TBool :-> TBool)
  OpNot -> TBool :-> TBool
  
----------------------------------------------------------------
-- Recursion schemes stuff
----------------------------------------------------------------

-- | Descend into data type and replace nodes that match predicate function
replaceCata
  :: (Recursive t, Corecursive t)
  => (Base t t -> Maybe t)
  -> t -> t
replaceCata fun = cata $ \x ->
  case fun x of Nothing -> embed x
                Just x' -> x'


cataM :: (Monad m, Traversable (Base t), Recursive t)
      => (Base t a -> m a)
      -> (t        -> m a)
cataM f = go
  where
    go = (f =<<) . mapM go . project



{-
(e -> Base t (e -> a) -> a)
((->) e (Base t ((->) e a) -> a))
(Reader e · Base t · Reader e) a -> a
-}

rcata :: Recursive t
      => (e -> Base t (e -> a) -> a)
      -> (e -> t -> a)
rcata f = go
  where
    go e = f e . fmap (flip go) . project


data Tree a = Leaf a
            | Branch (Tree a) a (Tree a)
            deriving Show
makeBaseFunctor ''Tree

retree :: TreeF Int a -> Maybe (Tree Int)
retree (LeafF n) = Just $ Branch (Leaf 0) n (Leaf 0)
retree _         = Nothing


-- step :: (Int -> TreeF Int (Int -> IO Int) -> IO Int)
-- step s = \case
--   LeafF   n     -> do print ("Leaf",n, s)
--                       return (n+s)
--   BranchF a n b -> do print ("Branch", n, s)
--                       na <- a (s+n)
--                       nb <- b (s+n)
--                       return $ na + nb
