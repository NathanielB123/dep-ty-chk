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

SemCtx : Set₁
SemCtx = Set

SemTy : Set → Set
SemTy Γ = Γ → U

data Ctx where
  ε   : Ctx
  _,_ : ∀ Γ → Ty Γ → Ctx

data Tm  : ∀ Γ → SemTy ⟦ Γ ⟧c → Set

data Ty where
  ⊥'  : Ty Γ
  Π'  : ∀ A → Ty (Γ , A) → Ty Γ
  El' : Tm Γ (λ _ → ⊥') → Ty Γ

⟦_⟧T : Ty Γ → SemTy ⟦ Γ ⟧c

εs : SemCtx
εs = ⊤

_,s_ : ∀ Γ → SemTy Γ → SemCtx
Γ ,s A = Σ Γ (El ∘ A)

⟦ ε ⟧c = εs
⟦ Γ , A ⟧c = ⟦ Γ ⟧c ,s ⟦ A ⟧T

Πsem : ∀ {Γ} A → SemTy (Γ ,s A) → SemTy Γ
Πsem A B ρ = Π' (A ρ) (B ∘ (ρ ,_))

SemVal : ∀ Γ → SemTy Γ → Set
SemVal _ A = ∀ ρ → El (A ρ)

⟦_⟧tm : ∀ {Γ A} → Tm Γ A → SemVal ⟦ Γ ⟧c A

⟦ ⊥'     ⟧T _ = ⊥'
⟦ Π' A B ⟧T   = Πsem ⟦ A ⟧T ⟦ B ⟧T
⟦ El' M  ⟧T   = ⊥-elim ∘ ⟦ M ⟧tm

SemSub : SemCtx → SemCtx → Set
SemSub Γ Δ = Γ → Δ

semwk :  ∀ {Γ} A → SemSub (Γ ,s A) Γ
semwk _ = proj₁

sem<_> : ∀ {Γ A} (M : SemVal Γ A) → SemSub Γ (Γ ,s A)
sem< M > Γ = Γ , M Γ

data Var : ∀ Γ → SemTy ⟦ Γ ⟧c → Set where
  vz : ∀ {Γ A} → Var (Γ , A) (⟦ A ⟧T ∘ semwk ⟦ A ⟧T)
  vs : ∀ {Γ A B} → Var Γ B → Var (Γ , A) (B ∘ semwk ⟦ A ⟧T)

⟦_⟧v : ∀ {Γ A} → Var Γ A → SemVal ⟦ Γ ⟧c A
⟦ vz ⟧v (ρ , M) = M
⟦ vs x ⟧v (ρ , M) = ⟦ x ⟧v ρ

data Tm where
  var : ∀ {Γ A} → Var Γ A → Tm Γ A
  app : ∀ {Γ A B} → Tm Γ (Πsem A B) → (N : Tm Γ A) → Tm Γ (B ∘ sem< ⟦ N ⟧tm >)
  lam : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Πsem ⟦ A ⟧T B)

appsem : ∀ {Γ A B} → SemVal Γ (Πsem A B) → (N : SemVal Γ A) 
       → SemVal Γ (B ∘ sem< N >)
appsem M N ρ = (M ρ) (N ρ)

⟦ var x   ⟧tm     = ⟦ x ⟧v
⟦ app M N ⟧tm     = appsem ⟦ M ⟧tm ⟦ N ⟧tm
⟦ lam M   ⟧tm ρ N = ⟦ M ⟧tm (ρ , N)
  