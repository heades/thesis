{-# LANGUAGE NoMonomorphismRestriction #-}
{- |
Module      :  Lang.DTT.Eval
Description :  The evaluator for DTT.
Copyright   :  (c) Harley Eades
License     : 
  "THE BEER-WARE LICENSE" (Revision 42):
  As long as you retain this notice you can do whatever you want with
  this stuff. If we meet some day, and you think this stuff is worth it,
  you can buy me a beer in return Harley Eades.

Maintainer  :  harley-eades@uiowa.edu
Stability   :  experimental
Portability :  portable

This module implements the evaluator for Dualized Type Theory.
-}
module Lang.DTT.Eval (eval) where

import Prelude
import Data.List
import Control.Monad.IO.Class

import Unbound.LocallyNameless hiding (rec, apply)

import Lang.DTT.Syntax
import Lang.DTT.PrettyPrint

--Check to see if a variable is free in a term.
isFreeIn' x (Var a) acc = return (if (elem x acc) then False else (x == a))
isFreeIn' x (Lam b) acc = do
  (y, t) <- unbind b
  a <- isFreeIn' x t (y:acc)
  return a
isFreeIn' x (Mu b) acc = do
  (y, (t1,t2)) <- unbind b
  a1 <- isFreeIn' x t1 (y:acc)
  a2 <- isFreeIn' x t2 (y:acc)
  return (a1 || a2)
isFreeIn' x (Prod t1 t2) acc = do
  a1 <- isFreeIn' x t1 acc
  a2 <- isFreeIn' x t2 acc
  return (a1 || a2)
isFreeIn' x (CoProd t1 t2) acc = do
  a1 <- isFreeIn' x t1 acc
  a2 <- isFreeIn' x t2 acc
  return (a1 || a2)
isFreeIn' x (In1 t) acc = isFreeIn' x t acc
isFreeIn' x (In2 t) acc = isFreeIn' x t acc
isFreeIn' x Triv acc = return False
isFreeIn' x (Rec _ t1 b) acc = do
  (z, t2) <- unbind b
  a1 <- isFreeIn' x t1 acc
  a2 <- isFreeIn' x t2 (z:acc)
  return (a1 || a2)
isFreeIn x t = isFreeIn' x t []

-- Used for debugging.
showApplied r msg = do
  s <- pPrint r
  liftIO $ putStrLn (msg++": "++s)

{- The evaluator.  Terms are reduced to normal forms.
   If we are not SN this will loop. :-)

   RVarRight has precedence over RRet. -}
eval :: MonadIO m => Fresh m => Term -> m Term

eval Triv = return Triv

eval (Var x) = return (Var x)

eval (Lam binding) = do
  (x,e) <- unbind binding
  e' <- eval e
  return (Lam (bind x e'))

eval (Prod t1 t2) = do
  e1 <- eval t1
  e2 <- eval t2
  return (Prod e1 e2)

eval (CoProd a b) = do
  e1 <- eval a
  e2 <- eval b
  case (e1, e2) of
    (Mu b2, t2) -> -- RNegGen
        do (x, (t, t')) <- unbind b2
           y <- fresh x
           let s = subst x (Mu (bind y (CoProd (Var y) t2, (Var x)))) t in
             let s' = subst x (Mu (bind y (CoProd (Var y) t2, (Var x)))) t' in
               do _ <- showApplied (Mu (bind x (s,s'))) "RNegGen"
                  eval (Mu (bind x (s,s'))) 
    _ -> return (CoProd e1 e2)

eval (In1 t) = do
  e <- eval t
  return (In1 e)

eval (In2 t) = do
  e <- eval t
  return (In2 e)

eval (Mu b1) = do
  (z,(t1,t2)) <- unbind b1
  e1 <- eval t1
  e2 <- eval t2
  case (e1, e2) of
    (Lam b2, CoProd t1 t2) -> -- RImp
        do (x,t) <- unbind b2 
           let r = (Mu (bind z (t1, Mu (bind x (t2, t)))))  in
             do _ <- showApplied r "RImp"
                eval r

    (CoProd t1 t2, Lam b2) -> -- RImpBar
        do (x, t) <- unbind b2
           let r = (Mu (bind z (Mu (bind x (t2, t)),t1))) in
             do _ <- showApplied r "RImpBar"
                eval r

    (Prod t1 t2, In1 t) -> -- RAnd1
        let r = (Mu (bind z (t1,t))) in
          do _ <- showApplied r "Applied"
             eval r    

    (Prod t1 t2, In2 t) -> -- RAnd2
        let r = (Mu (bind z (t2,t))) in
          do _ <- showApplied r "RAnd2"
             eval r

    (In1 t, Prod t1 t2) -> -- RAndBar1
        let r = (Mu (bind z (t, t1))) in
          do _ <- showApplied r "RAndBar1"
             eval r

    (In2 t, Prod t1 t2) -> -- RAndBar2
        let r = (Mu (bind z (t, t2))) in
          do _ <- showApplied r "RAndBar2"
             eval r

    (Mu b2, Var x) -> -- RVarRight
        do (y, (t,t')) <- unbind b2
           let s = subst y (Var x) t in
             let s' = subst y (Var x) t' in
               let r = (Mu (bind z (s,s'))) in
                 do _ <- showApplied r "RVarRight"
                    eval r

    (In1 t, Mu b2) -> -- RIn1Left
        do (x, (t1,t2)) <- unbind b2
           let e1 = subst x (In1 (Var x)) t1 in
             let e2 = subst x (In1 (Var x)) t2 in
               let r = (Mu (bind z (t, (Mu (bind x (e1, e2)))))) in
                 do _ <- showApplied r "RIn1Left"
                    eval r

    (In2 t, Mu b2) -> -- RIn2Left
        do (x, (t1,t2)) <- unbind b2
           let e1 = subst x (In2 (Var x)) t1 in
             let e2 = subst x (In2 (Var x)) t2 in
               let r = (Mu (bind z (t, (Mu (bind x (e1, e2)))))) in
                 do _ <- showApplied r "RIn2Left"
                    eval r

    (Mu b2, In1 t) -> -- RIn1Right
        do (x, (t1, t2)) <- unbind b2
           let e1 = subst x (In1 (Var x)) t1 in
             let e2 = subst x (In1 (Var x)) t2 in
               let r = (Mu (bind z (Mu (bind x (e1,e2)),t))) in
                 do _ <- showApplied r "RIn1Right"
                    eval r

    (Mu b2, In2 t) -> -- RIn2Right
        do (x, (t1, t2)) <- unbind b2
           let e1 = subst x (In2 (Var x)) t1 in
             let e2 = subst x (In2 (Var x)) t2 in
               let r = (Mu (bind z (Mu (bind x (e1,e2)),t))) in
                 do _ <- showApplied r "RIn2Right"
                    eval r

    (Prod t1 t2,Mu b2) -> -- RProdLeft
        do (x, (t3, t4)) <- unbind b2
           x1 <- fresh x
           x2 <- fresh x
           let e1 = subst x (Prod (Var x1) (Var x2)) t3 in
             let e2 = subst x (Prod (Var x1) (Var x2)) t4 in
               let r = (Mu (bind z (t1, Mu (bind x1 (Mu (bind x2 (e1,e2)), t2))))) in
                 do _ <- showApplied r "RProdLeft"
                    eval r

    (Mu b2,Prod t1 t2) -> -- RProdRight
        do (x, (t3, t4)) <- unbind b2
           x1 <- fresh x
           x2 <- fresh x
           let e1 = subst x (Prod (Var x1) (Var x2)) t3 in
             let e2 = subst x (Prod (Var x1) (Var x2)) t4 in
               let r = (Mu (bind z (Mu (bind x1 (t2,Mu (bind x2 (e2,e1)))),t1))) in
                 do _ <- showApplied r "RProdRight"
                    eval r
    
    (Triv, Mu b2) -> -- RTrivLeft
        do (x,(t,t')) <- unbind b2
           let s = subst x Triv t in
             let s' = subst x Triv t' in
               let r = (Mu (bind z (s',s))) in
                 do _ <- showApplied r "RTrivLeft"
                    eval r

    (Mu b2, Triv) -> -- RTrivRight
        do (x, (t,t')) <- unbind b2
           let s = subst x Triv t in
             let s' = subst x Triv t' in
               let r = (Mu (bind z (s,s'))) in
                 do _ <- showApplied r "RTrivRight"
                    eval r 

    (Mu b2, Lam b3) -> -- RLamRight
        do (y, (t2,t3)) <- unbind b2
           let s2 = subst y (Lam b3) t2 in
             let s3 = subst y (Lam b3) t3 in
               let r = (Mu (bind z (s2,s3))) in
                 do _ <- showApplied r "RLamRight"
                    eval r

    (CoProd t1 t2, Mu b2) -> -- RStackLeft
        do (x,(t3,t4)) <- unbind b2
           x1 <- fresh x
           x2 <- fresh x
           let s3 = subst x (CoProd (Var x1) (Var x2)) t3 in
             let s4 = subst x (CoProd (Var x1) (Var x2)) t4 in
               let r = (Mu (bind z (Mu (bind x1 (t2, Mu (bind x2 (s3,s4)))),t1))) in
                 do _ <- showApplied r "RStackLeft"
                    eval r

    (Mu b2, CoProd t1 t2) -> -- RStackRight
        do (x,(t3,t4)) <- unbind b2
           x1 <- fresh x
           x2 <- fresh x
           let s3 = subst x (CoProd (Var x1) (Var x2)) t3 in
             let s4 = subst x (CoProd (Var x1) (Var x2)) t4 in
               let r = (Mu (bind z (t1,Mu (bind x1 (Mu (bind x2 (s3,s4)),t2))))) in
                 do _ <- showApplied r "RStackRight"
                    eval r

    (Var x,Mu b2) -> -- RVarLeft
        do (y, (t,t')) <- unbind b2
           let s = subst y (Var x) t in
             let s' = subst y (Var x) t' in
               let r = (Mu (bind z (s',s))) in
                 do _ <- showApplied r "RVarLeft"
                    eval r

    (Mu b2, Mu b3) -> do
        (x, (a, b)) <- unbind b2
        (y, (c, d)) <- unbind b3
        f <- isFreeIn x a
        f' <- isFreeIn x d
        case (a,b) of
          (t1, Var y') | x /= y' && not f -> -- RMuLeft
            let r = (Mu (bind z (t1, Var y'))) in
              do _ <- showApplied r "RMuLeft"
                 eval r
          _ ->
              case (c,d) of
                (Var y', t1) | y /= y' && not f' -> -- RMuRight
                  let r = (Mu (bind z (t1,Var y'))) in
                    do _ <- showApplied r "RMuRight"
                       eval r

    (t, Var x) -> -- RRet               
        do 
          r <- isFreeIn x t
          case r of
            False | x == z -> 
              do _ <- showApplied t "RRet"                      
                 return t
            _ -> return (Mu b1)

    _ -> return (Mu (bind z (e1,e2)))

eval (Rec b1 t1 b2) = do -- RRec
  (x, t) <- unbind b1
  t1' <- apply (bind x (t,t)) t1 b2
  (z, t2) <- unbind b2
  let r = (Mu (bind z (t1',t2))) in
    do _ <- showApplied r "RRec" 
       eval r

-- Apply X.(T',T) t1 t2
apply :: Fresh m => (Bind TyName (Type,Type)) -> Term -> (Bind TmName Term) -> m Term
apply b1 t1 b2 = do
  (x, (t',t)) <- unbind b1
  (z, t2) <- unbind b2
  case (t',t) of
    (T_Var y, t) | x == y -> -- ApVar
      return (Prod t1 (Rec (bind x t) t1 (bind z t2)))
    (Unit _, a) -> -- ApTriv
      return Triv
    (CD a _ b, t) -> 
      case t1 of
        Prod c d -> -- ApAnd
            do e <- apply (bind x (a,t)) c (bind z t2)
               e' <- apply (bind x (a,t)) d (bind z t2)
               return (Prod e e')
        In1 c -> -- ApAndBar1
            do e <- apply (bind x (a,t)) c (bind z t2)
               return (In1 e)
        In2 c -> -- ApAndBar1
            do e <- apply (bind x (b,t)) c (bind z t2)
               return (In2 e)
