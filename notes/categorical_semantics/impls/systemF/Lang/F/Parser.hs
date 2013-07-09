{-# LANGUAGE NoMonomorphismRestriction, PackageImports #-}
{- |
Module      :  Lang.F.Parser
Description :  The parser for system F.
Copyright   :  (c) Harley Eades
License     : 
  "THE BEER-WARE LICENSE" (Revision 42):
  As long as you retain this notice you can do whatever you want with
  this stuff. If we meet some day, and you think this stuff is worth it,
  you can buy me a beer in return Harley Eades.

Maintainer  :  harley-eades@uiowa.edu
Stability   :  experimental
Portability :  portable

This module implements the parser for system F.
-}
module Lang.F.Parser where

import Prelude
import Data.List
import Data.Char
import Control.Applicative hiding ((<|>),many,optional)
import "mtl" Control.Monad.Identity hiding (fix)
import Control.Monad.IO.Class
import Control.Monad.State

import Unbound.LocallyNameless hiding (name,Infix,Val,Con,Equal,Refl, rec)
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as Token
import Text.Parsec.Language

import Lang.F.Syntax

-- State data type.
-- (name,type,Nothing) means we have a type def. but not the function def.
-- (name,type,Just term) means we have both a type def. and a function def.
type StateDefs = (TmName, Type, Maybe Term)

lexer = haskellStyle {
          Token.reservedNames   = ["forall", "inst", "with"],
          Token.reservedOpNames = ["fun"{-lambda-}, "tfun"{-type abs-}, "->", "=>", "|-"]
        }
tokenizer = Token.makeTokenParser lexer

ident      = Token.identifier tokenizer
reserved   = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer
parens     = Token.parens tokenizer
angles     = Token.angles tokenizer
brackets   = Token.brackets tokenizer
braces     = Token.braces tokenizer
ws         = Token.whiteSpace tokenizer
natural    = Token.natural tokenizer
dot        = Token.dot tokenizer
comma      = Token.comma tokenizer
colon      = Token.colon tokenizer

-- TODO: Get global state working.
exprParser = ws >> expr
typeParser = ws >> typeExpr

aterm = (parens expr) <|> tapp_parse <|> var
expr = try app_parse <|> lam <|> tlam 

-- The initial expression parsing table for types.
table = [[binOp AssocRight "->" (\d r -> Imp d r)]]
binOp assoc op f = Infix (reservedOp op >> return f) assoc
typeExprOps = buildExpressionParser table typeExprAtoms
typeExprAtoms = parens typeExpr <|> tyForall <|> tyVar
typeExpr = typeExprOps <|> typeExprAtoms

tyForall = do
  reserved "forall"
  var <- tyVarName
  dot
  ty <- typeExpr
  return $ Forall (bind var ty)

defnType = do
  name <- varName
  reservedOp ":"
  ty <- typeExpr
  return (TDef name ty)

defn = do
  name <- varName
  reservedOp ":="
  term <- expr
  return (Def name term)

atom a c = do
  reserved a
  return c

-- Parsers to be used by the expression parser.
-- fun x T => t  Lam
-- tfun X => t   TLam
lam_parse = do 
  reservedOp "fun"
  name <- varName
  ty <- typeExpr
  reservedOp "=>"
  body <- expr
  return . Lam ty . bind name $ body

tlam_parse = do
  reservedOp "tfun"
  name <- tyVarName
  reservedOp "=>"
  body <- expr
  return . TLam . bind name $ body

tapp_parse = do
  reserved "inst"
  t <- expr
  reserved "with"
  ty <- typeExpr
  return $ TApp ty t

app_parse = do
  ts <- many aterm
  return . foldl1 App $ ts
       
unexpColon msg = unexpected (" : "++msg)

varName' f msg = do
  n <- ident
  when (f (head n)) $ unexpColon msg
  return . s2n $ n
varName = varName' isUpper "Term variables must begin with a lowercase letter."
tyVarName = varName' isLower "Type variables must begin with an uppercase letter."

var' p c = do 
  var_name <- p
  return (c var_name)  
var   = var' varName Var

tyVar  = var' tyVarName T_Var
lam    = lam_parse
tlam    = tlam_parse

ctxElement = do
  v <- varName
  colon
  ty <- typeExpr 
  return $ (v,ty)
  
parseCtx = do  
  t <- (sepBy ctxElement (char ','))
  return t

tJdg = do
  ctx <- parseCtx
  reservedOp "|-"
  t <- expr <?> "Term"
  colon
  ty <- typeExpr <?> "Type"
  eof
  return $ TJdg ctx t ty

parseType str = 
    case parse typeParser "" str of
      Left e  -> error $ show e
      Right r -> r

parseCtxEl :: String -> (Name Term, Type)
parseCtxEl str = 
    case parse ctxElement "" str of
      Left e  -> error $ show e
      Right r -> r

parserCtx :: String -> [(Name Term, Type)]
parserCtx str = 
    case parse parseCtx "" str of
      Left e  -> error $ show e
      Right r -> r

parseTJdg str = 
    case parse tJdg "[typing judgement]" str of
      Left e  -> error $ show e
      Right r -> r

parseTerm str = 
    case parse expr "" str of
      Left e  -> error $ show e
      Right r -> r

parseDef str = 
    case parse defn "" str of
      Left e  -> error $ show e
      Right r -> r


