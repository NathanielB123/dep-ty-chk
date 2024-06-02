{-# OPTIONS --rewriting --local-confluence-check #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; cong-app; subst; sym; dcong; dcong₂
  ; subst-application′)
  renaming (trans to _∙_)
open import Data.Nat using (ℕ; suc; zero)

open import Coincidences.Utils

module Coincidences.Syntax where

data Ctx : Set
data Ty  : Ctx → Set

variable
  Γ Δ θ Ξ : Ctx
  A : Ty Γ
  B : Ty Δ
  C : Ty θ
  D : Ty Ξ

data U : Set
El : U → Set

data U where
  ⊥'  : U
  Π'  : ∀ A → (El A → U) → U

El ⊥' = ⊥
El (Π' A B) = ∀ x → El (B x)

⟦_⟧c : Ctx → Set

SemTy : Ctx → Set
SemTy Γ = ⟦ Γ ⟧c → U

data Ctx where
  ε   : Ctx
  _,_ : ∀ Γ → Ty Γ → Ctx

data Tm  : ∀ Γ → SemTy Γ → Set

data Ty where
  ⊥'  : Ty Γ
  Π'  : ∀ A → Ty (Γ , A) → Ty Γ
  El' : Tm Γ (λ _ → ⊥') → Ty Γ

⟦_⟧T : Ty Γ → SemTy Γ

⟦ ε ⟧c = ⊤
⟦ Γ , A ⟧c = Σ ⟦ Γ ⟧c (El ∘ ⟦ A ⟧T)

-- Todo: Tidy this up (semantic contexts??)
-- I wonder if in general contexts holding syntactic types is more trouble than
-- it is worth...
Πsem : (A : SemTy Γ) → (Σ ⟦ Γ ⟧c (El ∘ A) → U) → SemTy Γ
Πsem A B ρ = Π' (A ρ) (B ∘ (ρ ,_))

SemVal : ∀ Γ → SemTy Γ → Set
SemVal _ A = ∀ ρ → El (A ρ)

⟦_⟧tm : ∀ {A} → Tm Γ A → SemVal Γ A

⟦ ⊥'     ⟧T _ = ⊥'
⟦ Π' A B ⟧T ρ = Π' (⟦ A ⟧T ρ) (⟦ B ⟧T ∘ (ρ ,_))
⟦ El' M  ⟧T   = ⊥-elim ∘ ⟦ M ⟧tm

semwk : ∀ A → SemTy Γ → SemTy (Γ , A)
semwk _ = _∘ proj₁

sem<_> : ∀ {A} (M : SemVal Γ A) → (Σ ⟦ Γ ⟧c (El ∘ A) → U) → SemTy Γ
sem< M > A ρ = A (ρ , M ρ)

data Var : ∀ Γ → SemTy Γ → Set where
  vz : Var (Γ , A) (semwk A ⟦ A ⟧T)
  vs : ∀ {B} → Var Γ B → Var (Γ , A) (semwk A B)

⟦_⟧v : ∀ {A} → Var Γ A → SemVal Γ A
⟦ vz ⟧v (ρ , M) = M
⟦ vs x ⟧v (ρ , M) = ⟦ x ⟧v ρ

data Tm where
  var : ∀ {A} → Var Γ A → Tm Γ A
  app : ∀ {A B} → Tm Γ (Πsem A B) → (N : Tm Γ A) → Tm Γ (sem< ⟦ N ⟧tm > B)
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (Πsem ⟦ A ⟧T B)

appsem : ∀ {A B} → SemVal Γ (Πsem A B) → (N : SemVal Γ A) 
       → SemVal Γ (sem< N > B)
appsem M N ρ = (M ρ) (N ρ)

⟦ var x   ⟧tm     = ⟦ x ⟧v
⟦ app M N ⟧tm     = appsem ⟦ M ⟧tm ⟦ N ⟧tm
⟦ lam M   ⟧tm ρ N = ⟦ M ⟧tm (ρ , N)
