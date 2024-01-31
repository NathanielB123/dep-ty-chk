{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality using (subst; cong)
  renaming (sym to sym≡)
open import Function.Base using (id)

open import Syntax
open import Equations.Coercions

module Nf where

data VarCoe : ∀ (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set

data Var : ∀ (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set where
  vz : ∀ {Γ A} → Var (Γ , A) (A [ wk ]T) vz
  vs : ∀ {Γ A B x} → Var Γ A x → Var (Γ , B) (A [ wk ]T) (x [ wk ])

data VarCoe where
  coe : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
      → Var Γ₁ A₁ M₁ → VarCoe Γ₂ A₂ M₂

data Ne : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set
data Nf : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set
data NeCoe : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set
data NfCoe : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set

data Ne where
  var : ∀ {Γ A x} → Var Γ A x → Ne Γ A x
  app : ∀ {Γ A B} {M : Tm Γ (Π A B)} {N : Tm Γ A} 
      → NeCoe Γ (Π A B) M → NfCoe Γ A N 
      → Ne Γ (B [ < N > ]T) (app M N)

data Nf where
  ne    : ∀ {Γ A M} → Ne Γ A M → Nf Γ A M
  lam   : ∀ {Γ A B M} → NfCoe (Γ , A) B M → Nf Γ (Π A B) (lam M)

data NeCoe where
  coe :  ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
      → Ne Γ₁ A₁ M₁ → NeCoe Γ₂ A₂ M₂

data NfCoe where
  coe :  ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
        → Nf Γ₁ A₁ M₁ → NfCoe Γ₂ A₂ M₂

data NfSub : ∀ (Γ Δ : Ctx) → Sub Γ Δ → Set where
  <_> : ∀ {Γ A M} → Nf Γ A M → NfSub Γ (Γ , A) < M >
  _↑_  : ∀ {Γ Δ δ} → NfSub Γ Δ δ → ∀ A → NfSub (Γ , A [ δ ]T) (Δ , A) (δ ↑ A)

data NfSubCoe : ∀ (Γ Δ : Ctx) → Sub Γ Δ → Set where
  coe : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ δ₁ δ₂} → δ₁ ≈s δ₂ → NfSub Γ₁ Δ₁ δ₁ → NfSubCoe Γ₂ Δ₂ δ₂ 

data NfWk : ∀ (Γ Δ : Ctx) → Sub Γ Δ → Set where
  wk   : ∀ {Γ A} → NfWk (Γ , A) Γ wk
  _↑_  : ∀ {Γ Δ δ} → NfWk Γ Δ δ → ∀ A → NfWk (Γ , A [ δ ]T) (Δ , A) (δ ↑ A)

data NfWkCoe : ∀ (Γ Δ : Ctx) → Sub Γ Δ → Set where
  coe : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ δ₁ δ₂} → δ₁ ≈s δ₂ → NfWk Γ₁ Δ₁ δ₁ → NfWkCoe Γ₂ Δ₂ δ₂ 

coe-nf : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
       → NfCoe Γ₁ A₁ M₁ → NfCoe Γ₂ A₂ M₂
coe-nf p (coe q M) = coe (p ∙ q) M

coe-ne : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
       → NeCoe Γ₁ A₁ M₁ → NeCoe Γ₂ A₂ M₂
coe-ne p (coe q M) = coe (p ∙ q) M

coe-v : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
       → VarCoe Γ₁ A₁ M₁ → VarCoe Γ₂ A₂ M₂
coe-v p (coe q x) = coe (p ∙ q) x

coe-wk₁ : ∀ {Γ₁ Γ₂ Δ δ} (Γ : Γ₁ ≈C Γ₂) → NfWkCoe Γ₁ Δ δ 
       → NfWkCoe Γ₂ Δ (coe-s₁ Γ δ) 
coe-wk₁ p (coe q δ) = coe (sym (coh-s₁ p) ∙ q) δ

coe-wk₂ : ∀ {Γ Δ₁ Δ₂ δ} (Δ : Δ₁ ≈C Δ₂) → NfWkCoe Γ Δ₁ δ 
       → NfWkCoe Γ Δ₂ (coe-s₂ Δ δ) 
coe-wk₂ p (coe q δ) = coe (sym (coh-s₂ p) ∙ q) δ

coe-wk-nf₂ : ∀ {Γ Δ₁ Δ₂ δ} (Δ : Δ₁ ≈C Δ₂) → NfWk Γ Δ₁ δ 
           → NfWkCoe Γ Δ₂ (coe-s₂ Δ δ) 
coe-wk-nf₂ p δ = coe-wk₂ p (coe rfl δ)

coe-sub₁ : ∀ {Γ₁ Γ₂ Δ δ} (Γ : Γ₁ ≈C Γ₂) → NfSubCoe Γ₁ Δ δ 
       → NfSubCoe Γ₂ Δ (coe-s₁ Γ δ) 
coe-sub₁ p (coe q δ) = coe (sym (coh-s₁ p) ∙ q) δ

coe-sub₂ : ∀ {Γ Δ₁ Δ₂ δ} (Δ : Δ₁ ≈C Δ₂) → NfSubCoe Γ Δ₁ δ 
       → NfSubCoe Γ Δ₂ (coe-s₂ Δ δ) 
coe-sub₂ p (coe q δ) = coe (sym (coh-s₂ p) ∙ q) δ

coe-sub-nf₂ : ∀ {Γ Δ₁ Δ₂ δ} (Δ : Δ₁ ≈C Δ₂) → NfSub Γ Δ₁ δ 
           → NfSubCoe Γ Δ₂ (coe-s₂ Δ δ) 
coe-sub-nf₂ p δ = coe-sub₂ p (coe rfl δ)
