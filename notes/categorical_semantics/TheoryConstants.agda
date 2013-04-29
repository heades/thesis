module TheoryConstants where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Bool

data Type : Set where
     S : Type
     U : Type

data Term : Set where
     var  : ℕ → Term
     cons : Term 
     fun  : List ℕ → Term

Ctx : Set
Ctx = List (ℕ × Type)

data _∈_ {A : Set}(x : A) : List A -> Set where 
     hd : forall {xs} → x ∈ (x ∷ xs)
     tl : forall {y xs} → x ∈ xs -> x ∈ (y ∷ xs)

open import Data.Maybe
open import Relation.Binary.PropositionalEquality
data False : Set where
record True : Set where 
term_listIn : Ctx → List ℕ → Set
term_listIn [] [] = True
term_listIn _ [] = False
term_listIn  Γ (t ∷ ts) = (t ∈ (Data.List.map proj₁ Γ)) × (term_listIn Γ ts)

data _⊢_∶_ (Γ : Ctx) : Term → Type → Set where
   Ax : ∀ {x T} → ((x  , T) ∈ Γ) → Γ ⊢ var x ∶ T
   Fun : ∀ {L T} → (term_listIn Γ L) → Γ ⊢ fun L ∶ T


