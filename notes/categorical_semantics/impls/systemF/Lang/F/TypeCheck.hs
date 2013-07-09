{-# LANGUAGE NoMonomorphismRestriction, PackageImports #-}
{- |
Module      :  Lang.F.TypeCheck
Description :  The type checker for system F.
Copyright   :  (c) Harley Eades
License     : 
  "THE BEER-WARE LICENSE" (Revision 42):
  As long as you retain this notice you can do whatever you want with
  this stuff. If we meet some day, and you think this stuff is worth it,
  you can buy me a beer in return Harley Eades.

Maintainer  :  harley-eades@uiowa.edu
Stability   :  experimental
Portability :  portable

This module implements the type checker for system F.
-}
module Lang.F.TypeCheck where

import Prelude
import System.Exit
import Lang.F.Syntax
import Lang.F.Parser
import Unbound.LocallyNameless hiding (name)

-- Need this type.
typeCheck :: Fresh m => TJdg -> m (Maybe Type)

typeCheck (TJdg ctx (Var n) ty) = do
    let i = n `lookup` ctx in
      case i of
        Nothing  -> return Nothing
        Just ty' -> return $ (case ty of
                                Hole -> Just ty
                                _ -> if ty `aeq` ty' then Just ty else Nothing)

{- Each function call be either the canonical type or just a Hole
   we need to handle both. -}
typeCheck (TJdg ctx (Lam dty b) (Imp dty' rty)) = 
    do     
      (n,t) <- unbind b 
      r <- typeCheck (TJdg ((n,dty):ctx) t rty)
      return r

typeCheck (TJdg ctx (TLam btm) (Forall bty)) = 
    do
      a <- unbind2 btm bty -- Open the function body and 
                           -- the type using the same names.
      case a of
        Nothing -> return Nothing
        Just (n,t, nty, ty) -> typeCheck (TJdg ctx t ty)        
  
typeCheck (TJdg ctx (App t1 t2) ty) = 
    do
      r1 <- typeCheck (TJdg ctx t1 (Imp Hole ty)) 
      r2 <- typeCheck (TJdg ctx t2 Hole) 
      return (r1 && r2)

typeCheck (TJdg ctx tm ty) = do 
  return False
