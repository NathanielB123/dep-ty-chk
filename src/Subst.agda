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
open import NoSub

-- Remove all explicit substitutions from terms
module Subst where

rm-sub : ∀ {Γ A} (M : Tm Γ A) → NsCoe Γ A M

_[_]ns : ∀ {Γ Δ A M} → NsCoe Γ A M → (δ : Sub Δ Γ) 
       → NsCoe Δ (A [ δ ]T) (M [ δ ])

sort-sub :  ∀ {Γ Δ} (δ : Sub Γ Δ) → NsWkCoe Γ Δ δ ⊎ NsSubCoe Γ Δ δ
sort-sub (coe₁ Γ δ) with sort-sub δ
... | inj₁ δ  = inj₁ (coe-wk₁ (trs Γ rfl) δ)
... | inj₂ δ = inj₂ (coe-sub₁ (trs Γ rfl) δ)
sort-sub (coe₂ Δ δ) with sort-sub δ
... | inj₁ δ  = inj₁ (coe-wk₂ (trs Δ rfl) δ)
... | inj₂ δ = inj₂ (coe-sub₂ (trs Δ rfl) δ)
sort-sub wk = inj₁ (coe rfl wk)
sort-sub < M > = inj₂ < rm-sub M >ns
sort-sub (δ ↑ A) with sort-sub δ
... | inj₁ δ = inj₁ (δ ↑wk A)
... | inj₂ δ = inj₂ (δ ↑sub A)

_[_]nswkcoe : ∀ {Γ Δ A M δ} → NsCoe Γ A M → NsWkCoe Δ Γ δ 
         → NsCoe Δ (A [ δ ]T) (M [ δ ])
_[_]nswk : ∀ {Γ Δ A M δ} → Ns Γ A M → NsWkCoe Δ Γ δ 
         → NsCoe Δ (A [ δ ]T) (M [ δ ])

_[_]vwkcoe : ∀ {Γ Δ A M δ} → VarCoe Γ A M → NsWk Δ Γ δ 
         → VarCoe Δ (A [ δ ]T) (M [ δ ])
_[_]vwk  : ∀ {Γ Δ A M δ} → Var Γ A M → NsWkCoe Δ Γ δ 
         → VarCoe Δ (A [ δ ]T) (M [ δ ])

coe p M [ δ ]nswkcoe 
  = coe-ns ⟦ p [ coh-s₂ _ ]≋ ⟧ (M [ coe-wk₂ (sym (≈t↑≈C p)) δ ]nswk)

var x [ δ ]nswk = var-ns (x [ δ ]vwk)
app M N [ δ ]nswk = coe-ns ⟦ app[] ⟧⁻¹ (app-ns (M [ δ ]nswkcoe) (N [ δ ]nswk))
lam M [ δ ]nswk = coe ⟦ lam[] ⟧⁻¹ (lam (M [ δ ↑wk _ ]nswkcoe))

coe p x [ δ ]vwkcoe 
  = coe-v ⟦ p [ coh-s₂ (sym (≈t↑≈C p)) ]≋ ⟧ 
          (x [ coe-wk₂ (sym (≈t↑≈C p)) (coe rfl δ) ]vwk)

x [ coe p wk ]vwk = coe ⟦ rfl [ p ∙ ⟦ wk≈ (coh-T (≈s↑≈C₂ p)) ⟧ ]≋ ⟧ (vs x)
vz [ coe p (δ ↑ A) ]vwk 
  = coe (⟦ ⟦ vz (,-inj₂ (≈s↑≈C₂ p)) ⟧ [ p ]≋ ⟧ ∙ ⟦ vz[] ⟧⁻¹) vz
vs x [ coe p (δ ↑ A) ]vwk 
  = coe-v (⟦ ⟦ coh-t _ [ ⟦ wk≈ AB≈ ⟧ ]≋ ⟧ [ p ]≋ ⟧ ∙ ⟦ wk-comm _ _ ⟧⁻¹ 
  ∙ ⟦ ⟦ sym (coh-t (sym (coh-T (sym ΔΓ≈)))) [ coh-s₂ ΔΓ≈ ]≋ ⟧ [ rfl ]≋ ⟧)
    (vs-ns (x [ coe-wk₂ (,-inj₁ (≈s↑≈C₂ p)) (coe rfl δ) ]vwk))
  where ΔΓ≈ = ,-inj₁ (≈s↑≈C₂ p)
        AB≈ = ,-inj₂ (≈s↑≈C₂ p)

_[_]nssubcoe : ∀ {Γ Δ A M δ} → NsCoe Γ A M → NsSubCoe Δ Γ δ 
         → NsCoe Δ (A [ δ ]T) (M [ δ ])
_[_]nssub : ∀ {Γ Δ A M δ} → Ns Γ A M → NsSubCoe Δ Γ δ 
         → NsCoe Δ (A [ δ ]T) (M [ δ ])

_[_]vsubcoe : ∀ {Γ Δ A M δ} → VarCoe Γ A M → NsSub Δ Γ δ 
         → NsCoe Δ (A [ δ ]T) (M [ δ ])
_[_]vsub  : ∀ {Γ Δ A M δ} → Var Γ A M → NsSubCoe Δ Γ δ 
         → NsCoe Δ (A [ δ ]T) (M [ δ ])

coe p M [ δ ]nssubcoe 
  = coe-ns ⟦ p [ coh-s₂ _ ]≋ ⟧ (M [ coe-sub₂ (sym (≈t↑≈C p)) δ ]nssub)

var x [ δ ]nssub = x [ δ ]vsub
app M N [ δ ]nssub 
  = coe-ns ⟦ app[] ⟧⁻¹ (app-ns (M [ δ ]nssubcoe) (N [ δ ]nssub))
lam M [ δ ]nssub = coe ⟦ lam[] ⟧⁻¹ (lam (M [ δ ↑sub _ ]nssubcoe))

coe p x [ δ ]vsubcoe 
  = coe-ns ⟦ p [ coh-s₂ (sym (≈t↑≈C p)) ]≋ ⟧ 
          (x [ coe-sub₂ (sym (≈t↑≈C p)) (coe rfl δ) ]vsub)

vz [ coe p < M > ]vsub 
  = coe (⟦ ⟦ vz (,-inj₂ (≈s↑≈C₂ p)) ⟧ [ p ]≋ ⟧ ∙ ⟦ vz<> ⟧⁻¹) M
vz [ coe p (δ ↑ A) ]vsub 
  = coe (⟦ ⟦ vz (,-inj₂ (≈s↑≈C₂ p)) ⟧ [ p ]≋ ⟧ ∙ ⟦ vz[] ⟧⁻¹) (var vz)
vs x [ coe p < M > ]vsub 
  = coe (⟦ ⟦ coh-t (sym (coh-T (sym (,-inj₁ (≈s↑≈C₂ p))))) 
         [ ⟦ wk≈ (,-inj₂ (≈s↑≈C₂ p)) ⟧ ]≋ ⟧ [ p ]≋ ⟧ 
  ∙ ⟦ wk-<>-id _ ⟧⁻¹ ∙ sym (coh-t _)) (var x)
vs x [ coe p (δ ↑ A) ]vsub
  = coe-ns (⟦ ⟦ coh-t _ [ ⟦ wk≈ AB≈ ⟧ ]≋ ⟧ [ p ]≋ ⟧ ∙ ⟦ wk-comm _ _ ⟧⁻¹ 
    ∙ ⟦ ⟦ sym (coh-t (sym (coh-T (sym ΔΓ≈)))) [ coh-s₂ ΔΓ≈ ]≋ ⟧ [ rfl ]≋ ⟧)
      ((x [ coe-sub₂ (,-inj₁ (≈s↑≈C₂ p)) (coe rfl δ) ]vsub) 
      [ coe rfl wk ]nswkcoe)
    where ΔΓ≈ = ,-inj₁ (≈s↑≈C₂ p)
          AB≈ = ,-inj₂ (≈s↑≈C₂ p)

M [ δ ]ns with sort-sub δ 
... | inj₁ δ = M [ δ ]nswkcoe
... | inj₂ δ = M [ δ ]nssubcoe

rm-sub (coe p M) = coe-ns ⟦ coh p ⟧⁻¹ (rm-sub M)
rm-sub (app M N) = app-ns (rm-sub M) (rm-sub N)
rm-sub (lam M) = coe rfl (lam (rm-sub M))
rm-sub (M [ δ ]) = rm-sub M [ δ ]ns
rm-sub vz = coe rfl (var vz)
