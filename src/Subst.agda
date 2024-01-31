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

-- For now, let's assume we can normalise terms
postulate
  nf : ∀ {Γ A} → (M : Tm Γ A) → NfCoe Γ A M

_↑wk_ : ∀ {Γ Δ δ} → NfWkCoe Γ Δ δ → ∀ A → NfWkCoe (Γ , A [ δ ]T) (Δ , A) (δ ↑ A)
coe p δ ↑wk A 
  = coe ⟦ p ↑ coh-T (sym (≈s↑≈C₂ p)) ⟧ (δ ↑ coe-T (sym (≈s↑≈C₂ p)) A)

_↑sub_ : ∀ {Γ Δ δ} → NfSubCoe Γ Δ δ → ∀ A 
       → NfSubCoe (Γ , A [ δ ]T) (Δ , A) (δ ↑ A)
coe p δ ↑sub A 
  = coe ⟦ p ↑ coh-T (sym (≈s↑≈C₂ p)) ⟧ (δ ↑ coe-T (sym (≈s↑≈C₂ p)) A)

nf-sub : ∀ {Γ Δ} (δ : Sub Γ Δ) → NfWkCoe Γ Δ δ ⊎ NfSubCoe Γ Δ δ
nf-sub (coe₁ Γ δ) with nf-sub δ
... | inj₁ δ  = inj₁ (coe-wk₁ (trs Γ rfl) δ)
... | inj₂ δ = inj₂ (coe-sub₁ (trs Γ rfl) δ)
nf-sub (coe₂ Δ δ) with nf-sub δ
... | inj₁ δ  = inj₁ (coe-wk₂ (trs Δ rfl) δ)
... | inj₂ δ = inj₂ (coe-sub₂ (trs Δ rfl) δ)
nf-sub wk = inj₁ (coe rfl wk)
nf-sub < M > with nf M
... | coe p M′ = inj₂ (coe ⟦ [ ≈t↑≈C p , ≈t↑≈T p ]< p > ⟧ < M′ >)
nf-sub (δ ↑ A) with nf-sub δ
... | inj₁ δ = inj₁ (δ ↑wk A)
... | inj₂ δ = inj₂ (δ ↑sub A)

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

coe p M [ δ ]nfwkcoe 
  = coe-nf ⟦ p [ coh-s₂ _ ]≋ ⟧ (M [ coe-wk₂ (sym (≈t↑≈C p)) δ ]nfwk)

ne  M [ δ ]nfwk with coe p M′ ← M [ δ ]newk = coe p (ne M′)
lam M [ δ ]nfwk = coe ⟦ lam[] ⟧⁻¹ (lam (M [ δ ↑wk _ ]nfwkcoe))

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

_[_]vsub : ∀ {Γ Δ A M δ} → Var Γ A M → NfSubCoe Δ Γ δ 
         → NfCoe Δ (A [ δ ]T) (M [ δ ])
vz [ coe p < M > ]vsub 
  = coe (⟦ ⟦ vz (,-inj₂ (≈s↑≈C₂ p)) ⟧ [ p ]≋ ⟧ ∙ ⟦ vz<> ⟧⁻¹) M
vz [ coe p (δ ↑ A) ]vsub 
  = coe (⟦ ⟦ vz (,-inj₂ (≈s↑≈C₂ p)) ⟧ [ p ]≋ ⟧ ∙ ⟦ vz[] ⟧⁻¹) (ne (var vz))
vs x [ coe p < M > ]vsub 
  = coe (⟦ ⟦ coh-t (sym (coh-T (sym (,-inj₁ (≈s↑≈C₂ p))))) 
         [ ⟦ wk (,-inj₁ (≈s↑≈C₂ p)) (,-inj₂ (≈s↑≈C₂ p)) ⟧ ]≋ ⟧ [ p ]≋ ⟧ 
  ∙ ⟦ wk-<>-id _ ⟧⁻¹ ∙ sym (coh-t _)) (ne (var x))
vs x [ coe p (δ ↑ A) ]vsub 
  with coe q M ← x [ coe-sub-nf₂ (,-inj₁ (≈s↑≈C₂ p)) δ ]vsub
    = coe-nf (⟦ ⟦ coh-t _ [ ⟦ wk ΔΓ≈ (coh-T (sym ΔΓ≈)) ⟧ ]≋ ⟧ 
    [ p ∙ ⟦ coh-s₂ _ ↑ sym (,-inj₂ (≈s↑≈C₂ p)) ⟧ 
  ∙ ⟦ sym (coh-s₂ ΔΓ≈) ↑ coh-T (sym ΔΓ≈) ⟧ ]≋ ⟧ 
  ∙ ⟦ wk-comm (coe-t (sym (coh-T (sym ΔΓ≈))) _) _ ⟧⁻¹ 
  ∙ ⟦ ⟦ sym (coh-t _) [ coh-s₂ ΔΓ≈ ]≋ ⟧ [ rfl ]≋ ⟧ 
  ∙ ⟦ q [ ⟦ wk (≈t↑≈C q) ((sym (coh-T (sym ΔΓ≈))) 
    [ coh-s₂ ΔΓ≈ ∙ coh-s₁ (sym (≈t↑≈C q)) ]T≈) ⟧ ]≋ ⟧) 
    (M [ coe rfl wk ]nfwk)
  where ΔΓ≈ = ,-inj₁ (≈s↑≈C₂ p)
