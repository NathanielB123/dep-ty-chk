{-# OPTIONS --rewriting --prop --show-irrelevant #-}

open import Coincidences.Utils
open import Coincidences.Substitutions.Single.Weak
open import Coincidences.Substitutions.Parallel.Common
open import Coincidences.Substitutions.Parallel.Sub 
  (λ A M → M [ wk ]wtm) (λ A M → refl)

module Coincidences.Bootstrap.Syntax where

open import Coincidences.Syntax 
  renaming (Var to SemiVar; Tm to SemiTm; Tm≡ to SemiTm≡; Var≡ to SemiVar≡) 
  public

module TypeOf where
  type-of-v : ∀ {A} → SemiVar Γ A → Ty Γ
  type-of-v {Γ = _ , A} vz = A [ wk ]w
  type-of-v (vs x) = type-of-v x [ wk ]w

  type-of-v≡ : ∀ {A} (x : SemiVar Γ A) → ⟦ type-of-v x ⟧T ≡ A
  type-of-v≡ vz = refl
  type-of-v≡ (vs x) = cong (_∘ proj₁) (type-of-v≡ x)
open TypeOf

data Var : ∀ Γ → Ty Γ → Set
data Tm : ∀ Γ → Ty Γ → Set

↓v : Var Γ A → SemiVar Γ ⟦ A ⟧T 
↓tm : Tm Γ A → SemiTm Γ ⟦ A ⟧T

data Var where
  vz : Var (Γ , A) (A [ wk ]w)
  vs : Var Γ B → Var (Γ , A) (B [ wk ]w)

data Tm where
   var : Var Γ A → Tm Γ A
   app : ∀ {Γ A} {B : Ty (Γ , A)} {ΠAB} → Tm Γ ΠAB 
       → (N : Tm Γ A) 
       → ⟦ ΠAB ⟧T ≡ Πsem ⟦ A ⟧T ⟦ B ⟧T
       → Tm Γ (B [ < ↓tm N > ])
   lam : Tm (Γ , A) B → Tm Γ (Π' A B)

private module Congruences where
  Var≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
       → Var Γ₁ A₁ ≡ Var Γ₂ A₂
  Var≡ refl refl = refl

  Tm≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
      → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂
  Tm≡ refl refl = refl
open Congruences public

↓v vz = vz
↓v (vs x) = vs (↓v x)

↓tm (var x)      = var (↓v x)
↓tm (app M N p)  = app (subst (SemiTm _) p (↓tm M)) (↓tm N)
↓tm (lam M)      = lam (↓tm M)

↑v : ∀ {A} (x : SemiVar Γ A) → Var Γ (type-of-v x) 
↑v vz = vz 
↑v (vs x) = vs (↑v x)
