{-# OPTIONS --prop --show-irrelevant --rewriting --local-confluence-check #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys

module Coincidences.Substitutions.Common where

[]-helper : ∀ {Γ Δ A A[]} (B : SemTy (Γ ,s A)) (δ : SemSub Δ Γ) 
               (p : A[] ≡ A ∘ δ) 
          → subst (SemTy ∘ (_ ,s_)) (sym p) (B ∘ (δ ↑s _))
          ≡ (λ (ρ , x) → B (δ ρ , subst (λ AB → El (AB ρ)) p x))
[]-helper B δ refl = refl

[]v-helper : ∀ {Γ A B} (p : A ≡ B)
           → subst (SemVal (Γ ,s A)) (cong (_∘ semwk _) p) semvz
           ≡ (λ (ρ , x) → subst (λ AB → El (AB ρ)) p x)
[]v-helper refl = refl

[]tm-helper : ∀ {Γ Δ} (δ : SemSub Δ Γ) {A[]} 
                {A : SemTy Γ} {B : SemTy (Γ ,s A)} 
                (M : SemVal _ B) (A≡ : A[] ≡ _) B≡
            → subst (SemVal Δ) (Πsem≡ refl A≡ B≡) (λ ρ x → (M ∘ (δ ↑s A)) 
                    (ρ , subst (λ A[] → El (A[] ρ)) A≡ x))
            ≡ (λ ρ N → M (ρ , N)) ∘ δ
[]tm-helper _ _ refl refl = refl


↑-helper : ∀ {Γ Δ} A (δ : SemSub Δ Γ) A[] (A≡ : A[] ≡ _) 
    → (λ (ρ , M) → δ ρ , subst (λ AB → El (AB ρ)) A≡ M)
      ≡ subst (λ A′ → SemSub (Δ ,s A′) (Γ ,s A)) (sym A≡) (δ ↑s A)
↑-helper A δ A[] refl = refl
