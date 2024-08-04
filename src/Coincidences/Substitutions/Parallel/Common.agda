{-# OPTIONS --prop --show-irrelevant --rewriting #-}
--local-confluence-check

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys

module Coincidences.Substitutions.Parallel.Common where

εsem = ⊤

semwk* : ∀ Γ → SemSub ⟦ Γ ⟧c εsem
semwk* ε = id
semwk* (Γ , A) = semwk* Γ ∘ semwk ⟦ A ⟧T

_,sub_ : ∀ {Γ Δ A} (δ : SemSub Δ Γ) → SemVal Δ (A ∘ δ) 
          → SemSub Δ (Γ ,s A) 
(δ ,sub M) ρ = δ ρ , M ρ

↑[]-helper : ∀ {Γ Δ} (δ : SemSub Δ Γ) {A} {A[]} (A≡ : A[] ≡ A ∘ δ) 
           → coe (sym (cong₂ SemSub (cong (Δ ,s_) A≡) refl)) (δ ↑s A)
           ≡ (δ ∘ semwk _) 
           ,sub subst (λ A′ → SemVal _ (A′ ∘ semwk A[])) A≡ semvz
↑[]-helper δ refl = refl

[]lam-helper : ∀ {Γ Δ} (δ : SemSub Δ Γ) A {A[]} (A≡ : A[] ≡ A ∘ δ )
             → (λ ρ → subst (λ AB → El (AB (ρ .proj₁))) A≡ (ρ .proj₂))
             ≡  subst (λ A′ → SemVal (Δ ,s _) (A′ ∘ semwk A[])) A≡ proj₂
[]lam-helper δ A refl = refl

[]lam≡-helper : ∀ {Γ Δ} (δ : SemSub Δ Γ) {A B A[] δ↑A} (M : SemVal (Γ ,s A) B) 
                  (p : A[] ≡ A ∘ δ) (q : _ ≡ δ↑A) r
              → subst (SemVal Δ) r (lamsem (subst (SemVal (Δ ,s A[]) ∘ (B ∘_)) q
                      (M ∘ coe (sym (cong₂ SemSub (cong (_,s_ Δ) p) refl)) 
                      (δ ↑s A))))
              ≡ lamsem M ∘ δ
[]lam≡-helper _ _ refl refl refl = refl

semvz-helper : ∀ {Δ A₁ A₂} (A≡ : A₁ ≡ A₂) 
             → subst (SemVal (Δ ,s A₁) ∘ (_∘ semwk A₁)) A≡ semvz
             ≡ (λ (ρ , M) → subst (λ AB → El (AB ρ)) A≡ M)
semvz-helper refl = refl
