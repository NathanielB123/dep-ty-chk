{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function.Base using (id)

open import Syntax
open import Equations.Coercions
open import Equations.Equations
open import Equations.Injectivity
open import Nf

-- Normalisation with no care taken to show termination
module Norm where

{-# TERMINATING #-}
nf : ∀ {Γ A} → (M : Tm Γ A) → NfCoe Γ A M
_[_]nf : ∀ {Γ Δ A M} → NfCoe Γ A M → (δ : Sub Δ Γ) 
       → NfCoe Δ (A [ δ ]T) (M [ δ ])
_[_]ne : ∀ {Γ Δ A M} → NeCoe Γ A M → (δ : Sub Δ Γ) 
       → NfCoe Δ (A [ δ ]T) (M [ δ ])
_[_]v  : ∀ {Γ Δ A M} → Var Γ A M → (δ : Sub Δ Γ) → NfCoe Δ (A [ δ ]T) (M [ δ ])
appnf : ∀ {Γ A B M} → NfCoe Γ (Π A B) M → ∀ N
      → NfCoe Γ (B [ < N > ]T) (app M N)

nf (coe A M) = coe-nf ⟦ coh A ⟧⁻¹ (nf M)
nf (app M N) = appnf (nf M) N
nf (lam M) = coe rfl (lam (nf M))
nf (M [ δ ]) = nf M [ δ ]nf
nf vz = coe rfl (ne (var vz))

coe p (ne  M) [ δ ]nf 
  = coe-nf ⟦ p [ coh-s₂ _ ]≋ ⟧ (coe rfl M [ coe-s₂ (sym (≈t↑≈C p)) δ ]ne)
coe p (lam M) [ δ ]nf 
  = coe (⟦ p [ coh-s₂ (sym (≈t↑≈C p)) ]≋ ⟧ 
  ∙ ⟦ lam[] ⟧⁻¹) (lam (M [ coe-s₂ (sym (≈t↑≈C p)) δ ↑ _ ]nf))

-- We do a little coercing
coe p (var x) [ δ ]ne 
  = coe-nf ⟦ p [ coh-s₂ _ ]≋ ⟧ (x [ coe-s₂ (sym (≈t↑≈C p)) δ ]v)
coe p (app M N) [ δ ]ne 
  = coe-nf (⟦ p [ coh-s₂ (sym (≈t↑≈C p)) ]≋ ⟧ ∙ ⟦ app[] ⟧⁻¹) 
           (appnf (M [ coe-s₂ (sym (≈t↑≈C p)) δ ]ne) 
                  (_ [ coe-s₂ (sym (≈t↑≈C p)) δ ]))

appnf (coe p (ne  M)) N 
  = coe-nf ⟦ app (p ∙ coh-t (≈t↑≈T p)) rfl ⟧ 
           (ne-coe (app-coe (coe (sym (coh-t (≈t↑≈T p))) M) (nf N)))
appnf (coe p (lam M)) N 
  = coe-nf (⟦ app p (coh-t _) ⟧ ∙ ⟦ β ⟧⁻¹) 
           (M [ < coe-t (sym (Π-inj₁ (≈t↑≈T p))) N > ]nf)

x [ coe₁ Γ δ ]v = coe-nf ⟦ rfl [ ⟦ coh₁ Γ ⟧⁻¹ ]≋ ⟧ (x [ δ ]v)
x [ coe₂ Δ δ ]v 
  = coe-nf (⟦ ⟦ _≋t_.coh _ ⟧ [ ⟦ coh₂ _ ⟧⁻¹ ]≋ ⟧) 
           (coe ⟦ coh (coh-1-T (symsym Δ) _ ⁻¹) ⟧⁻¹ (ne (var x)) [ δ ]nf)
x [ wk ]v = coe rfl (ne (var (vs x)))
vz [ < M > ]v = coe-nf ⟦ vz<> ⟧⁻¹ (nf M)
vs x [ < M > ]v = coe ⟦ wk-<>-id _ ⟧⁻¹ (ne (var x))
vz [ δ ↑ A ]v = coe ⟦ vz[] ⟧⁻¹ (ne (var vz))
vs x [ δ ↑ A ]v = coe-nf ⟦ wk-comm _ δ ⟧⁻¹ (x [ δ ]v [ wk ]nf)
