{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances #-}
{- |
Module      :  Lang.F.Syntax
Description :  The syntax for DTT.
Copyright   :  (c) Harley Eades
License     : 
  "THE BEER-WARE LICENSE" (Revision 42):
  As long as you retain this notice you can do whatever you want with
  this stuff. If we meet some day, and you think this stuff is worth it,
  you can buy me a beer in return Harley Eades.

Maintainer  :  harley-eades@uiowa.edu
Stability   :  experimental
Portability :  portable

This module implements the syntax definition for system F.
We use the locally nameless representation with the aid of the unbound
library.
-}
module Lang.F.Syntax (Prog(..), TyName, Type(..), TmName, Term(..), TJdg(..)) where

import Prelude
import Data.List
import Unbound.LocallyNameless
import Unbound.LocallyNameless.Alpha
import Data.Typeable

type TyName = Name Type              -- Type names
data Type =
    T_Var TyName                     -- Type variable
  | Imp Type Type                    -- Implication
  | Forall (Bind TyName Type)        -- Universal Quantification  
  | Hole                             -- A hole.
  deriving (Show)

type TmName = Name Term              -- Term names
data Term =
    Var TmName                       -- Term variable
  | Lam Type (Bind TmName Term)      -- Lambda abstraction
  | TLam (Bind TyName Term)          -- Type Abstraction
  | App Term Term                    -- Application
  | TApp Type Term                   -- Type Application
  deriving (Show, Typeable)

data TJdg = TJdg [(TmName,Type)] Term Type
          deriving Show

data Prog =
    Def TmName Term
  | TDef TmName Type
  deriving (Show, Typeable)

$(derive [''Type, ''Term])
instance Alpha Type
instance Alpha Term

instance Subst Type Type where
  isvar (T_Var x) = Just (SubstName x)
  isvar _ = Nothing
instance Subst Type Term

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing
instance Subst Term Type

-- Typing Contexts
data Context = List (Term, Type)
