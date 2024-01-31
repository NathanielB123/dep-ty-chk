{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)

open import Syntax
open import Equations.Coercions
open import Equations.Equations
open import Equations.Injectivity
open import Nf

module Subst where

_↑nf_ : ∀ {Γ Δ δ} → NfWkCoe Γ Δ δ → ∀ A → NfWkCoe (Γ , A [ δ ]T) (Δ , A) (δ ↑ A)
coe p δ ↑nf A 
  = coe ⟦ p ↑ coh-T (sym (≈s↑≈C₂ p)) ⟧ (δ ↑ coe-T (sym (≈s↑≈C₂ p)) A)

_[_]nfwkcoe : ∀ {Γ Δ A M δ} → NfCoe Γ A M → NfWkCoe Δ Γ δ 
         → NfCoe Δ (A [ δ ]T) (M [ δ ])
_[_]nfwk : ∀ {Γ Δ A M δ} → Nf Γ A M → NfWkCoe Δ Γ δ 
         → NfCoe Δ (A [ δ ]T) (M [ δ ])

_[_]newkcoe  : ∀ {Γ Δ A M δ} → NeCoe Γ A M → NfWkCoe Δ Γ δ 
             → NeCoe Δ (A [ δ ]T) (M [ δ ])
_[_]newk  : ∀ {Γ Δ A M δ} → Ne Γ A M → NfWkCoe Δ Γ δ 
         → NeCoe Δ (A [ δ ]T) (M [ δ ])

_[_]vwkcoe : ∀ {Γ Δ A M δ} → VarCoe Γ A M → NfWk Δ Γ δ 
         → VarCoe Δ (A [ δ ]T) (M [ δ ])
_[_]vwk  : ∀ {Γ Δ A M δ} → Var Γ A M → NfWkCoe Δ Γ δ 
         → VarCoe Δ (A [ δ ]T) (M [ δ ])

-- Eventually we will have an NfSubCoe and ⊤ will be replaced with that
nf-sub : ∀ {Γ Δ} (δ : Sub Γ Δ) → NfWkCoe Γ Δ δ ⊎ ⊤
nf-sub (coe₁ Γ δ) with nf-sub δ
... | inj₁ δ  = inj₁ (coe-wk₁ (trs Γ rfl) δ)
... | inj₂ tt = inj₂ tt
nf-sub (coe₂ Δ δ) with nf-sub δ
... | inj₁ δ  = inj₁ (coe-wk₂ (trs Δ rfl) δ)
... | inj₂ tt = inj₂ tt
nf-sub wk = inj₁ (coe rfl wk)
nf-sub < M > = inj₂ tt
nf-sub (δ ↑ A) with nf-sub δ
... | inj₁ δ = inj₁ (δ ↑nf A)
... | inj₂ tt = inj₂ tt

coe p M [ δ ]nfwkcoe 
  = coe-nf ⟦ p [ coh-s₂ _ ]≋ ⟧ (M [ coe-wk₂ (sym (≈t↑≈C p)) δ ]nfwk)

ne  M [ δ ]nfwk with coe p M′ ← M [ δ ]newk = coe p (ne M′)
lam M [ δ ]nfwk = coe ⟦ lam[] ⟧⁻¹ (lam (M [ δ ↑nf _ ]nfwkcoe))

coe p M [ δ ]newkcoe 
  = coe-ne ⟦ p [ coh-s₂ _ ]≋ ⟧ (M [ coe-wk₂ (sym (≈t↑≈C p)) δ ]newk)

var x [ δ ]newk with coe p x′ ← x [ δ ]vwk = coe p (var x′)
app M N [ δ ]newk = coe ⟦ app[] ⟧⁻¹ (app (M [ δ ]newkcoe) (N [ δ ]nfwkcoe))

coe p x [ δ ]vwkcoe 
  = coe-v ⟦ p [ coh-s₂ (sym (≈t↑≈C p)) ]≋ ⟧ 
          (x [ coe-wk-nf₂ (sym (≈t↑≈C p)) δ ]vwk)
x [ coe p wk ]vwk 
  = coe ⟦ rfl [ p ∙ ⟦ wk (sym (≈s↑≈C₂ p)) (coh-T (≈s↑≈C₂ p)) ⟧ ]≋ ⟧ (vs x)
vz [ coe p (δ ↑ A′) ]vwk 
  = coe (⟦ ⟦ vz (,-inj₂ (≈s↑≈C₂ p)) ⟧ [ p ]≋ ⟧ ∙ ⟦ vz[] ⟧⁻¹) vz
vs x [ coe p (δ ↑ A) ]vwk 
  with coe q x′ ← x [ coe-wk-nf₂ (,-inj₁ (≈s↑≈C₂ p)) δ ]vwk 
  = coe (⟦ ⟦ coh-t _ [ ⟦ wk ΔΓ≈ (coh-T (sym ΔΓ≈)) ⟧ ]≋ ⟧ 
    [ p ∙ ⟦ coh-s₂ _ ↑ sym (,-inj₂ (≈s↑≈C₂ p)) ⟧ 
  ∙ ⟦ sym (coh-s₂ ΔΓ≈) ↑ coh-T (sym ΔΓ≈) ⟧ ]≋ ⟧ 
  ∙ ⟦ wk-comm (coe-t (sym (coh-T (sym ΔΓ≈))) _) _ ⟧⁻¹ 
  ∙ ⟦ ⟦ sym (coh-t _) [ coh-s₂ ΔΓ≈ ]≋ ⟧ [ rfl ]≋ ⟧ 
  ∙ ⟦ q [ ⟦ wk (≈t↑≈C q) ((sym (coh-T (sym ΔΓ≈))) 
    [ coh-s₂ ΔΓ≈ ∙ coh-s₁ (sym (≈t↑≈C q)) ]T≈) ⟧ ]≋ ⟧) 
    (vs x′)
  where ΔΓ≈ = ,-inj₁ (≈s↑≈C₂ p)
