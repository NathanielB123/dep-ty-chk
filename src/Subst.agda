{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function.Base using (id)

open import Syntax
open import Equations.Coercions
open import Equations.Equations
open import Equations.Injectivity
open import Nf

module Subst where

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
  = coe-nf ⟦ p [ coh-s₂ _ ]≋ ⟧ (M [ coe-wk (sym (≈t↑≈C p)) δ ]nfwk)

ne  M [ δ ]nfwk with coe p M′ ← M [ δ ]newk = coe p (ne M′)
lam M [ δ ]nfwk = coe ⟦ lam[] ⟧⁻¹ (lam (M [ δ ↑nf _ ]nfwkcoe))

coe p M [ δ ]newkcoe 
  = coe-ne ⟦ p [ coh-s₂ _ ]≋ ⟧ (M [ coe-wk (sym (≈t↑≈C p)) δ ]newk)

var x [ δ ]newk with coe p x′ ← x [ δ ]vwk = coe p (var x′)
app M N [ δ ]newk = coe ⟦ app[] ⟧⁻¹ (app (M [ δ ]newkcoe) (N [ δ ]nfwkcoe))

coe p x [ δ ]vwkcoe 
  = coe-v ⟦ p [ coh-s₂ (sym (≈t↑≈C p)) ]≋ ⟧ (x [ coe₂ (sym (≈t↑≈C p)) δ ]vwk)

x [ coe₂ p wk ]vwk 
  = coe ⟦ rfl [ (sym (coh-s₂ p)) 
  ∙ ⟦ wk (sym p) (coh-T p) ⟧ ]≋ ⟧ (vs x)
vz [ coe₂ p (δ ↑ A) ]vwk 
  = coe (⟦ ⟦ vz (,-inj₂ p) ⟧ [ sym (coh-s₂ p) ]≋ ⟧ ∙ ⟦ vz[] ⟧⁻¹) vz
vs x [ coe₂ p (δ ↑ A) ]vwk with coe q x′ ← x [ coe₂ (,-inj₁ p) δ ]vwk 
  = coe (⟦ ⟦ coh-t _ [ ⟦ wk (,-inj₁ p) (coh-T (sym (,-inj₁ p))) ⟧ ]≋ ⟧ 
    [ sym (coh-s₂ p) ∙ ⟦ coh-s₂ _ ↑ sym (,-inj₂ p) ⟧ 
  ∙ ⟦ sym (coh-s₂ (,-inj₁ p)) ↑ coh-T (sym (,-inj₁ p)) ⟧ ]≋ ⟧ 
  ∙ ⟦ wk-comm (coe-t (sym (coh-T (sym (,-inj₁ p)))) _) _ ⟧⁻¹ 
  ∙ ⟦ ⟦ sym (coh-t _) [ coh-s₂ (,-inj₁ p) ]≋ ⟧ [ rfl ]≋ ⟧ 
  ∙ ⟦ q [ ⟦ wk (≈t↑≈C q) ((sym (coh-T (sym (,-inj₁ p)))) 
    [ coh-s₂ (,-inj₁ p) ∙ coh-s₁ (sym (≈t↑≈C q)) ]T≈) ⟧ ]≋ ⟧) 
    (vs x′)
