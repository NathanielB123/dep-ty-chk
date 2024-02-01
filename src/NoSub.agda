{-# OPTIONS --without-K #-}

open import Syntax
open import Equations.Equations
open import Equations.Coercions

module NoSub where

data NsCoe : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set
data Ns    : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set
data VarCoe  : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set
data Var     : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Set

data Var where
  vz : ∀ {Γ A} → Var (Γ , A) (A [ wk ]T) vz
  vs : ∀ {Γ A B x} → Var Γ A x → Var (Γ , B) (A [ wk ]T) (x [ wk ])

data VarCoe where
  coe : ∀ {Γ₁ Γ₂ A₁ A₂} {x₁ : Tm Γ₁ A₁} {x₂ : Tm Γ₂ A₂} (p : x₁ ≈t x₂) 
      → Var Γ₁ A₁ x₁ → VarCoe Γ₂ A₂ x₂

data Ns where
  var : ∀ {Γ A x} → Var Γ A x → Ns Γ A x
  app : ∀ {Γ A B} {M : Tm Γ (Π A B)} {N : Tm Γ A} 
      → NsCoe Γ (Π A B) M → Ns Γ A N 
      → Ns Γ (B [ < N > ]T) (app M N)
  lam : ∀ {Γ A B M} → NsCoe (Γ , A) B M → Ns Γ (Π A B) (lam M)

data NsCoe where
  coe : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
      → Ns Γ₁ A₁ M₁ → NsCoe Γ₂ A₂ M₂

coe-v : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
       → VarCoe Γ₁ A₁ M₁ → VarCoe Γ₂ A₂ M₂
coe-v p (coe q x) = coe (p ∙ q) x

coe-ns : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} (p : M₁ ≈t M₂) 
       → NsCoe Γ₁ A₁ M₁ → NsCoe Γ₂ A₂ M₂
coe-ns p (coe q x) = coe (p ∙ q) x

vs-ns : ∀ {Γ A B x} → VarCoe Γ A x → VarCoe (Γ , B) (A [ wk ]T) (x [ wk ])
vs-ns (coe p x) = coe ⟦ p [ ⟦ wk≈ (coh-T (sym (≈t↑≈C p))) ⟧ ]≋ ⟧ (vs x)

var-ns : ∀ {Γ A x} → VarCoe Γ A x → NsCoe Γ A x
var-ns (coe p x) = coe p (var x)

app-ns : ∀ {Γ A B} {M : Tm Γ (Π A B)} {N : Tm Γ A} 
      → NsCoe Γ (Π A B) M → NsCoe Γ A N 
      → NsCoe Γ (B [ < N > ]T) (app M N)
app-ns M (coe p N) 
  = coe ⟦ app ⟦ coh _ ⟧ p ⟧ (app (coe-ns ⟦ coh 
    (Π (≈t↑≈T p) (coh-T ⟦ ≈t↑≈C p , ≈t↑≈T p ⟧⁻¹) ⁻¹) ⟧⁻¹ M) N)

data NsSub : ∀ (Γ Δ : Ctx) → Sub Γ Δ → Set where
  <_> : ∀ {Γ A M} → Ns Γ A M → NsSub Γ (Γ , A) < M >
  _↑_  : ∀ {Γ Δ δ} → NsSub Γ Δ δ → ∀ A → NsSub (Γ , A [ δ ]T) (Δ , A) (δ ↑ A)

data NsSubCoe : ∀ (Γ Δ : Ctx) → Sub Γ Δ → Set where
  coe : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ δ₁ δ₂} → δ₁ ≈s δ₂ → NsSub Γ₁ Δ₁ δ₁ → NsSubCoe Γ₂ Δ₂ δ₂ 

data NsWk : ∀ (Γ Δ : Ctx) → Sub Γ Δ → Set where
  wk   : ∀ {Γ A} → NsWk (Γ , A) Γ wk
  _↑_  : ∀ {Γ Δ δ} → NsWk Γ Δ δ → ∀ A → NsWk (Γ , A [ δ ]T) (Δ , A) (δ ↑ A)

data NsWkCoe : ∀ (Γ Δ : Ctx) → Sub Γ Δ → Set where
  coe : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ δ₁ δ₂} → δ₁ ≈s δ₂ → NsWk Γ₁ Δ₁ δ₁ → NsWkCoe Γ₂ Δ₂ δ₂ 

<_>ns : ∀ {Γ A M} → NsCoe Γ A M → NsSubCoe Γ (Γ , A) < M >
< coe p M >ns = coe ⟦ < p >≈ ⟧ < M >

_↑sub_  : ∀ {Γ Δ δ} → NsSubCoe Γ Δ δ → ∀ A 
           → NsSubCoe (Γ , A [ δ ]T) (Δ , A) (δ ↑ A)
coe p δ ↑sub A 
  = coe ⟦ p ↑ coh-T (sym (≈s↑≈C₂ p)) ⟧ (δ ↑ coe-T (sym (≈s↑≈C₂ p)) A)

_↑wk_  : ∀ {Γ Δ δ} → NsWkCoe Γ Δ δ → ∀ A 
          → NsWkCoe (Γ , A [ δ ]T) (Δ , A) (δ ↑ A)
coe p δ ↑wk A = 
    coe ⟦ p ↑ coh-T (sym (≈s↑≈C₂ p)) ⟧ (δ ↑ coe-T (sym (≈s↑≈C₂ p)) A)

coe-wk₁ : ∀ {Γ₁ Γ₂ Δ δ} (Γ : Γ₁ ≈C Γ₂) → NsWkCoe Γ₁ Δ δ 
       → NsWkCoe Γ₂ Δ (coe-s₁ Γ δ) 
coe-wk₁ p (coe q δ) = coe (sym (coh-s₁ p) ∙ q) δ

coe-wk₂ : ∀ {Γ Δ₁ Δ₂ δ} (Δ : Δ₁ ≈C Δ₂) → NsWkCoe Γ Δ₁ δ 
       → NsWkCoe Γ Δ₂ (coe-s₂ Δ δ) 
coe-wk₂ p (coe q δ) = coe (sym (coh-s₂ p) ∙ q) δ

coe-sub₁ : ∀ {Γ₁ Γ₂ Δ δ} (Γ : Γ₁ ≈C Γ₂) → NsSubCoe Γ₁ Δ δ 
       → NsSubCoe Γ₂ Δ (coe-s₁ Γ δ) 
coe-sub₁ p (coe q δ) = coe (sym (coh-s₁ p) ∙ q) δ

coe-sub₂ : ∀ {Γ Δ₁ Δ₂ δ} (Δ : Δ₁ ≈C Δ₂) → NsSubCoe Γ Δ₁ δ 
       → NsSubCoe Γ Δ₂ (coe-s₂ Δ δ) 
coe-sub₂ p (coe q δ) = coe (sym (coh-s₂ p) ∙ q) δ
