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
     fun  : List Term → Term

Ctx : Set
Ctx = List (ℕ × Type)

data _∈_ {A : Set}(x : A) : List A -> Set where 
     hd : forall {xs} → x ∈ (x ∷ xs)
     tl : forall {y xs} → x ∈ xs -> x ∈ (y ∷ xs)

open import Data.Maybe
open import Relation.Binary.PropositionalEquality
data False : Set where
record True : Set where 
term_listIn : Ctx → List Term → Set
term_listIn [] [] = True
term_listIn _ [] = False
term_listIn  Γ ((var n) ∷ ts) = (n ∈ (Data.List.map proj₁ Γ)) × (term_listIn Γ ts)
term_listIn  Γ (_ ∷ ts) = False

data _⊢_∶_ (Γ : Ctx) : Term → Type → Set where
   Ax : ∀ {x T} → ((x  , T) ∈ Γ) → Γ ⊢ var x ∶ T
   Fun : ∀ {L T} → (term_listIn Γ L) → Γ ⊢ fun L ∶ T

subs : Term → ℕ → Term → Term
subs _ = {!!}

data _⊢_≈_∶_ (Γ : Ctx) : Term → Term → Type → Set where
  Refl : ∀ {t₁ T} → 
       Γ ⊢ t₁ ≈ t₁ ∶ T

  Sym : ∀ {t₁ t₂ T} → 
       Γ ⊢ t₁ ≈ t₂ ∶ T → 
       Γ ⊢ t₂ ≈ t₁ ∶ T

  Trans : ∀ {t₁ t₂ t₃ T} → 
       Γ ⊢ t₁ ≈ t₂ ∶ T → 
       Γ ⊢ t₂ ≈ t₃ ∶ T → 
       Γ ⊢ t₁ ≈ t₃ ∶ T

  Subst : ∀ {n t₁ t₂ t t′ T T′} →
       Γ ⊢ t₁ ≈ t₂ ∶ T →
       (((n ,′ T) ∈ Γ) → False) →
       (Γ ++ ((n ,′ T) ∷ [])) ⊢ t ≈ t′ ∶ T′ → 
       Γ ⊢ (subs t₁ n t) ≈ (subs t₂ n t′) ∶ T′ 
       