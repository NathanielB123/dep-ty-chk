{-# OPTIONS --without-K #-}

open import Syntax

module Equations.Coercions where

≈Ts↑≈C : ∀ {Γ₁ Γ₂} {Δ₁ : Tys Γ₁} {Δ₂ : Tys Γ₂} → Δ₁ ≈Ts Δ₂ → Γ₁ ≈C Γ₂

≋Ts↑≈C : ∀ {Γ₁ Γ₂} {Δ₁ : Tys Γ₁} {Δ₂ : Tys Γ₂} → Δ₁ ≋Ts Δ₂ → Γ₁ ≈C Γ₂
≋Ts↑≈C (ε Γ)   = Γ
≋Ts↑≈C (Δ , A) = ≈Ts↑≈C Δ

≈Ts↑≈C rfl = rfl
≈Ts↑≈C (trs (Δ  ¹) r) = ≋Ts↑≈C Δ ∙ ≈Ts↑≈C r
≈Ts↑≈C (trs (Δ ⁻¹) r) = sym (≋Ts↑≈C Δ) ∙ ≈Ts↑≈C r

_++≈_ : ∀ {Γ₁ Γ₂} {Δ₁ : Tys Γ₁} {Δ₂ : Tys Γ₂}
    → Γ₁ ≈C Γ₂ → Δ₁ ≈Ts Δ₂ → Γ₁ ++ Δ₁ ≈C Γ₂ ++ Δ₂
Γ ++≈ rfl = rfl
Γ ++≈ trs (ε Σ    ¹) Δ = Σ ∙ ((sym Σ ∙ Γ) ++≈ Δ) 
Γ ++≈ trs (ε Σ   ⁻¹) Δ = sym Σ ∙ ((Σ ∙ Γ) ++≈ Δ)
Γ ++≈ trs (Δ , A  ¹) p = ⟦ (≈Ts↑≈C Δ ++≈ Δ) , A ⟧ ∙ ((sym (≈Ts↑≈C Δ) ∙ Γ) ++≈ p)
Γ ++≈ trs (Δ , A ⁻¹) p = sym ⟦ (≈Ts↑≈C Δ ++≈ Δ) ,  A ⟧ ∙ ((≈Ts↑≈C Δ ∙ Γ) ++≈ p)

_++↭_ : ∀ {Γ₁ Γ₂} {Δ₁ : Tys Γ₁} {Δ₂ : Tys Γ₂}
    → Γ₁ ↭C Γ₂ → Δ₁ ↭Ts Δ₂ → Γ₁ ++ Δ₁ ↭C Γ₂ ++ Δ₂
Γ ++↭ (ε _ ¹) = Γ
Γ ++↭ (ε _ ⁻¹) = Γ
Γ ++↭ (Δ , A ¹) = trs Γ rfl ++≈ Δ , A ¹
Γ ++↭ (Δ , A ⁻¹) = trs (symsym Γ) rfl ++≈ Δ , A ⁻¹

coe-1-T : ∀ {Γ₁ Γ₂} → Γ₁ ↭C Γ₂ → Ty Γ₁ → Ty Γ₂
coh-1-T : ∀ {Γ₁ Γ₂} (Γ : Γ₁ ↭C Γ₂) A → coe-1-T Γ A ≋T A

coe-1-T p U = U
coe-1-T p (El M) = El (coe (U (trs p rfl) ¹) M)
coe-1-T p (Π A B) 
  = Π (coe-1-T p A) (coe-1-T (trs p rfl , sym ⟦ coh-1-T p A ⟧ ¹) B)

coh-1-T Γ U = U (trs (symsym Γ) rfl)
coh-1-T Γ (El M) = El ⟦ coh _ ⟧
coh-1-T Γ (Π A B) = Π ⟦ coh-1-T _ A ⟧ ⟦ coh-1-T _ B ⟧

coe-1-Ts : ∀ {Γ₁ Γ₂} → Γ₁ ↭C Γ₂ → Tys Γ₁ → Tys Γ₂
coh-1-Ts : ∀ {Γ₁ Γ₂} (Γ : Γ₁ ↭C Γ₂) Δ → coe-1-Ts Γ Δ ≋Ts Δ

coe-1-Ts Γ ε = ε
coe-1-Ts Γ (Δ , A) = coe-1-Ts Γ Δ , coe-1-T (Γ ++↭ (coh-1-Ts Γ Δ ⁻¹)) A

coh-1-Ts Γ ε = ε (trs (symsym Γ) rfl)
coh-1-Ts Γ (Δ , A) = ⟦ coh-1-Ts Γ Δ ⟧ , ⟦ coh-1-T _ A ⟧

coe-T : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → Ty Γ₁ → Ty Γ₂
coe-T rfl A = A
coe-T (trs p q) A = coe-1-T p (coe-T q A)

coh-T : ∀ {Γ₁ Γ₂} (Γ : Γ₁ ≈C Γ₂) {A : Ty Γ₁} → coe-T Γ A ≈T A
coh-T rfl = rfl
coh-T (trs p r) = coh-T r ∙ ⟦ coh-1-T p _ ⟧

coe-T≈ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} (p : Γ₁ ≈C Γ₂) (q : Δ₁ ≈C Δ₂) {A₁ A₂}
       → A₁ ≈T A₂ → coe-T p A₁ ≈T coe-T q A₂
coe-T≈ rfl q A = sym (coh-T q)  ∙ A
coe-T≈ (trs p r) q A = coe-T≈ r q A ∙ ⟦ coh-1-T p _ ⟧

coe-t :  ∀ {Γ₁ Γ₂ A₁ A₂} (A : A₁ ≈T A₂) → Tm Γ₁ A₁ → Tm Γ₂ A₂
coe-t rfl M = M
coe-t (trs p r) M = coe p (coe-t r M)

coh-t : ∀ {Γ₁ Γ₂ A₁} {A₂ : Ty Γ₂} (A : A₁ ≈T A₂) {M : Tm Γ₁ A₁} 
      → coe-t A M ≈t M
coh-t rfl = rfl
coh-t (trs p r) = coh-t r ∙ ⟦ coh p ⟧

coe-s₁ : ∀ {Γ₁ Γ₂ Δ} → Γ₁ ≈C Γ₂ → Sub Γ₁ Δ → Sub Γ₂ Δ
coe-s₁ rfl δ = δ
coe-s₁ (trs p r) δ = coe₁ p (coe-s₁ r δ)

coh-s₁ : ∀ {Γ₁ Γ₂ Δ} (Γ : Γ₁ ≈C Γ₂) {δ : Sub Γ₁ Δ} → coe-s₁ Γ δ ≈s δ
coh-s₁ rfl = rfl
coh-s₁ (trs p r) = coh-s₁ r ∙ ⟦ coh₁ p ⟧

coe-s₂ : ∀ {Γ Δ₁ Δ₂} → Δ₁ ≈C Δ₂ → Sub Γ Δ₁ → Sub Γ Δ₂
coe-s₂ rfl δ = δ
coe-s₂ (trs p r) δ = coe₂ p (coe-s₂ r δ)

coh-s₂ : ∀ {Γ Δ₁ Δ₂} (Δ : Δ₁ ≈C Δ₂) {δ : Sub Γ Δ₁} → coe-s₂ Δ δ ≈s δ
coh-s₂ rfl = rfl
coh-s₂ (trs p r) = coh-s₂ r ∙ ⟦ coh₂ p ⟧
