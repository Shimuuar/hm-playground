{-# LANGUAGE RecursiveDo #-}
-- |
module HM.Simple.Parser
  ( -- * Lexer
    Token(..)
  , tokenize
    -- * Parser
  , grammar
  , bindVariables
  , parse
  ) where

import Control.Applicative
import Data.Char
import Data.List (elemIndex)
import Text.Earley
import Text.Regex.Applicative

import HM.Simple.AST

----------------------------------------------------------------
-- Tokenizer
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

-- | Grammar of language. It's intentionally simple
grammar :: Grammar r (Prod r e Token (Expr String String))
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

-- | Bind all variables using label as variable names
bindVariables :: Eq a => Expr a a -> Expr a a
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

-- | Parse string as language expression
parse :: String -> Expr String String
parse s =
  case tokenize s of
    Nothing   -> error "Tokenization failed"
    Just toks -> case fullParses (parser grammar) toks of
      ([],e)  -> error $ "No parse: " ++ show (e :: Report String [Token])
      ([x],_) -> bindVariables x
      (_,e)   -> error $ "Multiple parses: " ++ show e
