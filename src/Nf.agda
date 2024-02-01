{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality using (subst; cong)
  renaming (sym to sym≡)
open import Function.Base using (id)

open import Syntax
open import Equations.Equations
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
      → NeCoe Γ (Π A B) M → Nf Γ A N 
      → Ne Γ (B [ < N > ]T) (app M N)

data Nf where
  ne  : ∀ {Γ A M} → Ne Γ A M → Nf Γ A M
  lam : ∀ {Γ A B M} → NfCoe (Γ , A) B M → Nf Γ (Π A B) (lam M)

data NeCoe where
  coe :  ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
      → Ne Γ₁ A₁ M₁ → NeCoe Γ₂ A₂ M₂

data NfCoe where
  coe :  ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
        → Nf Γ₁ A₁ M₁ → NfCoe Γ₂ A₂ M₂

coe-nf : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
       → NfCoe Γ₁ A₁ M₁ → NfCoe Γ₂ A₂ M₂
coe-nf p (coe q M) = coe (p ∙ q) M

coe-ne : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
       → NeCoe Γ₁ A₁ M₁ → NeCoe Γ₂ A₂ M₂
coe-ne p (coe q M) = coe (p ∙ q) M

coe-v : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
       → VarCoe Γ₁ A₁ M₁ → VarCoe Γ₂ A₂ M₂
coe-v p (coe q x) = coe (p ∙ q) x

app-coe : ∀ {Γ A B} {M : Tm Γ (Π A B)} {N : Tm Γ A} 
      → NeCoe Γ (Π A B) M → NfCoe Γ A N 
      → NeCoe Γ (B [ < N > ]T) (app M N)
app-coe M (coe p N) 
  = coe ⟦ app ⟦ coh _ ⟧ p ⟧ (app (coe-ne (sym (coh-t 
        ⟦ Π (≈t↑≈T p) (coh-T ⟦ ≈t↑≈C p , ≈t↑≈T p ⟧⁻¹) ⟧⁻¹)) M) N)

ne-coe : ∀ {Γ A M} → NeCoe Γ A M → NfCoe Γ A M
ne-coe (coe p M) = coe p (ne M)
