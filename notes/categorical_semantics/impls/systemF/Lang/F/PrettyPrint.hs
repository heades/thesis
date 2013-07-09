{- |
Module      :  Lang.DTT.PrettyPrint
Description :  The pretty printer for DTT.
Copyright   :  (c) Harley Eades
License     : 
  "THE BEER-WARE LICENSE" (Revision 42):
  As long as you retain this notice you can do whatever you want with
  this stuff. If we meet some day, and you think this stuff is worth it,
  you can buy me a beer in return Harley Eades.

Maintainer  :  harley-eades@uiowa.edu
Stability   :  experimental
Portability :  portable

This module implements the pretty printer for Dualized Type Theory.
-}
module Lang.DTT.PrettyPrint (pPrint, pPrintType) where

import Prelude
import Data.List
import Data.Char
import Control.Monad.IO.Class
import Control.Applicative hiding (many)

import Unbound.LocallyNameless hiding (rec, apply)

import Lang.DTT.Syntax

pPrintCut c = do
  s1 <- pPrint (fst c) 
  s2 <- pPrint (snd c)
  return ("("++s1++" * "++s2++")")

pPrint :: Fresh m => Term -> m String
pPrint Triv = return "Triv"

pPrint (Var n) = return $ name2String n

pPrint (Lam b) = do
  (x, t) <- unbind b
  strT <- pPrint t
  let strX = name2String x in
    return ("\\"++strX++"."++strT)

pPrint (Mu b) = do
  (x, c) <- unbind b
  strC <- pPrintCut c
  let strX = name2String x in
    return ("mu "++strX++"."++strC)

pPrint (Prod t1 t2) = do
  s1 <- pPrint t1
  s2 <- pPrint t2
  return ("("++s1++","++s2++")")

pPrint (CoProd t1 t2) = do
  s1 <- pPrint t1
  s2 <- pPrint t2
  return ("<"++s1++","++s2++">")

pPrint (In1 t) = do
  s <- pPrint t
  return ("in1 "++s)

pPrint (In2 t) = do
  s <- pPrint t
  return ("in2 "++s)

pPrint (Rec b1 t b2) = do
  (x, a) <- unbind b1
  (z, b) <- unbind b2
  s1 <- pPrintType a
  s2 <- pPrint b
  s3 <- pPrint t
  let sX = map toUpper $ name2String x in
    let sz = name2String z in
      return ("rec "++sz++" "++sX++"."++s1++" "++s3++" "++s2)

pPrintType :: Fresh m => Type -> m String
pPrintType (T_Var n) = return $ map toUpper $ name2String n

pPrintType (Base) = return "Base"

pPrintType (Unit Pos) = return "Unit +"

pPrintType (Unit Neg) = return "Unit -"

pPrintType (IS t1 Pos t2) = do
  s1 <- pPrintType t1
  s2 <- pPrintType t2
  return (s1 ++ " ->+ " ++ s2)

pPrintType (IS t1 Neg t2) = do
  s1 <- pPrintType t1
  s2 <- pPrintType t2
  return (s1 ++ " ->- " ++ s2)

pPrintType (CD t1 Pos t2) = do
  s1 <- pPrintType t1
  s2 <- pPrintType t2
  return (s1 ++ " /+\\ " ++ s2)

pPrintType (CD t1 Neg t2) = do
  s1 <- pPrintType t1
  s2 <- pPrintType t2
  return (s1 ++ " /-\\ " ++ s2)

pPrintType (Fix Pos b) = do
  (x,t) <- unbind b
  s <- pPrintType t
  let sX = map toUpper $ name2String x in
    return ("fix+ "++sX++"."++s)
