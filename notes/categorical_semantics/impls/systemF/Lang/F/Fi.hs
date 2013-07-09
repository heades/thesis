{-# LANGUAGE NoMonomorphismRestriction, PackageImports,
  TypeSynonymInstances, FlexibleInstances, UndecidableInstances #-}
{- |
Module      :  Lang.F.Fi
Description :  The interactive mode for system F.
Copyright   :  (c) Harley Eades
License     : 
  "THE BEER-WARE LICENSE" (Revision 42):
  As long as you retain this notice you can do whatever you want with
  this stuff. If we meet some day, and you think this stuff is worth it,
  you can buy me a beer in return Harley Eades.

Maintainer  :  harley-eades@uiowa.edu
Stability   :  experimental
Portability :  portable

This module implements the interactive mode for system F.
-}
module Lang.F.Fi where

import Prelude
import System.Exit
import Lang.F.Syntax
import Lang.F.Parser
import Lang.F.TypeCheck
import Control.Monad
import Control.Monad.IO.Class
import Unbound.LocallyNameless

prompt :: String
prompt = "F> "

main :: IO()
main = do
  putStr prompt
  command <- getLine
  case command of
    ":quit"         -> exitSuccess
    ":q"            -> exitSuccess    
    (':':'t':' ':j) -> 
                 let r = parseTJdg j in
                   (do 
                     b <- runFreshMT (typeCheck r) 
                     liftIO $ (case b of
                                 True  -> putStrLn "Type Checks"
                                 False -> putStrLn "Fails to Type Check")) >> main
    _               -> putStrLn ("You entered: "++command++".") >> main