{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function.Base using (id)

open import Syntax
open import Equations.Coercions
open import Equations.Equations
open import Equations.Injectivity
open import Nf

module Subst where

_[_]vwkcoe : ∀ {Γ Δ A M δ} → VarCoe Γ A M → NfWk Δ Γ δ 
         → VarCoe Δ (A [ δ ]T) (M [ δ ])

_[_]vwk  : ∀ {Γ Δ A M δ} → Var Γ A M → NfWkCoe Δ Γ δ 
         → VarCoe Δ (A [ δ ]T) (M [ δ ])

coe p x [ δ ]vwkcoe 
  = coe-v ⟦ p [ coh-s₂ (sym (≈t↑≈C p)) ]≋ ⟧ (x [ coe₂ (sym (≈t↑≈C p)) δ ]vwk)

x [ coe₂ p wk ]vwk 
  = coe ⟦ rfl [ (sym (coh-s₂ p)) 
  ∙ ⟦ wk (sym p) (coh-T p) ⟧ ]≋ ⟧ (vs x)
vz [ coe₂ p (δ ↑ A) ]vwk 
  = coe (⟦ ⟦ vz (≈C-inj₂ p) ⟧ [ sym (coh-s₂ p) ]≋ ⟧ ∙ ⟦ vz[] ⟧⁻¹) vz
vs x [ coe₂ p (δ ↑ A) ]vwk with coe q x′ ← x [ coe₂ (≈C-inj₁ p) δ ]vwk 
  = coe (⟦ ⟦ coh-t _ [ ⟦ wk (≈C-inj₁ p) (coh-T (sym (≈C-inj₁ p))) ⟧ ]≋ ⟧ 
    [ sym (coh-s₂ p) ∙ ⟦ coh-s₂ _ ↑ sym (≈C-inj₂ p) ⟧ 
  ∙ ⟦ sym (coh-s₂ (≈C-inj₁ p)) ↑ coh-T (sym (≈C-inj₁ p)) ⟧ ]≋ ⟧ 
  ∙ ⟦ wk-comm (coe-t (sym (coh-T (sym (≈C-inj₁ p)))) _) _ ⟧⁻¹ 
  ∙ ⟦ ⟦ sym (coh-t _) [ coh-s₂ (≈C-inj₁ p) ]≋ ⟧ [ rfl ]≋ ⟧ 
  ∙ ⟦ q [ ⟦ wk (≈t↑≈C q) ((sym (coh-T (sym (≈C-inj₁ p)))) 
    [ coh-s₂ (≈C-inj₁ p) ∙ coh-s₁ (sym (≈t↑≈C q)) ]T≈) ⟧ ]≋ ⟧) 
    (vs x′)
