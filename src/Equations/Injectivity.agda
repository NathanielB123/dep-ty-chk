{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function.Base using (id)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃)
  renaming (_,_ to infixl 6 _,_)

open import Syntax
open import Equations.EqUtils

module Equations.Injectivity where

data Is,C : Pred ctx where
  prf : ∀ {Γ} {A : Ty Γ} → Is,C (Γ , A)

≈C-inj₁ : ∀ {Γ₁ Γ₂ A₁ A₂} → Γ₁ , A₁ ≈C Γ₂ , A₂ → Γ₁ ≈C Γ₂
≈C-inj₁
  = lift-proofP Is,C (λ where prf prf refl → refl) 
    (λ where (_ , _ ¹) prf → prf; (_ , _ ⁻¹) prf → prf)
    (λ where .(Γ , _) (prf {Γ}) → Γ) (λ where prf prf (Γ , _) → Γ) prf prf

≈C-inj₂ : ∀ {Γ₁ Γ₂ A₁ A₂} → Γ₁ , A₁ ≈C Γ₂ , A₂ → A₁ ≈T A₂
≈C-inj₂
  = lift-proofP Is,C (λ where prf prf refl → refl) 
    (λ where (_ , _ ¹) prf → prf; (_ , _ ⁻¹) prf → prf) 
    {C = λ where _ prf → _}
    (λ where (_ , A) prf → A) (λ where prf prf (_ , A) → A) prf prf

,ε-disj : ∀ {Γ A} → ¬ Γ , A ≈C ε
,ε-disj (trs (ε  ¹) p) = ,ε-disj p
,ε-disj (trs (ε ⁻¹) p) = ,ε-disj p

U-diverge : ∀ {Γ} → Ty Γ → Set
U-diverge U = ⊥
U-diverge (El M) = ⊤
U-diverge (Π A B) = ⊤

Π-diverge : ∀ {Γ} → Ty Γ → Set
Π-diverge U = ⊤
Π-diverge (El _) = ⊤
Π-diverge (Π _ _) = ⊥

U-diverge≈ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} 
                  → A₁ ≈T A₂ → U-diverge A₁ ≡ U-diverge A₂
U-diverge≈ rfl = refl
U-diverge≈ (trs (U _    ¹) r) = U-diverge≈ r
U-diverge≈ (trs (El _   ¹) r) = U-diverge≈ r
U-diverge≈ (trs (Π _ _  ¹) r) = U-diverge≈ r
U-diverge≈ (trs (U _   ⁻¹) r) = U-diverge≈ r
U-diverge≈ (trs (El _  ⁻¹) r) = U-diverge≈ r
U-diverge≈ (trs (Π _ _ ⁻¹) r) = U-diverge≈ r

U-El-disj : ∀ {Γ₁ Γ₂} {M : Tm Γ₂ U} → ¬ El M ≈T U {Γ₁}
U-El-disj p = subst id (U-diverge≈ p) tt

πEl : ∀ {Γ} → Ty Γ → Maybe (Tm Γ U)
πEl U = nothing
πEl (El A) = just A
πEl (Π _ _) = nothing

πEl≈ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ 
     → πEl A₁ ≈Maybe[ *SymClosure _≋t_ ] πEl A₂
πEl≈ r = lift-proof πEl (λ where (U _)   → ⟦ nothing ⟧
                                 (El M)  → ⟦ just M ⟧
                                 (Π _ _) → ⟦ nothing ⟧) r

El-inj : ∀ {Γ₁ Γ₂} {M₁ : Tm Γ₁ U} {M₂ : Tm Γ₂ U} → El M₁ ≈T El M₂ → M₁ ≈t M₂
El-inj r = collapse* (just-inj (πEl≈ r))

πΠ₁ : ∀ {Γ} → Ty Γ → Maybe (Ty Γ)
πΠ₁ U       = nothing
πΠ₁ (El M)  = nothing
πΠ₁ (Π A B) = just A

πΠ≈₁ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ 
     → πΠ₁ A₁ ≈Maybe[ *SymClosure _≋T_ ] πΠ₁ A₂
πΠ≈₁ r = lift-proof πΠ₁ (λ where (U _)   → ⟦ nothing ⟧
                                 (El M)  → ⟦ nothing ⟧
                                 (Π A _) → ⟦ just A ⟧) r

Π-inj₁ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂} → Π A₁ B₁ ≈T Π A₂ B₂
       → A₁ ≈T A₂
Π-inj₁ r = collapse* (just-inj (πΠ≈₁ r))

∃πΠ₂ : ∀ {Γ} → Ty Γ → Maybe (∃ Ty)
∃πΠ₂ U       = nothing
∃πΠ₂ (El _)  = nothing
∃πΠ₂ (Π A B) = just (_ , B)

πΠ₂≈ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂  
     → ∃πΠ₂ A₁ ≈Maybe[ _≋Σ[ _≈T_ ]_ ] ∃πΠ₂ A₂
πΠ₂≈ r = lift-proof ∃πΠ₂ (λ where (U _)   → ⟦ nothing ⟧
                                  (El _)  → ⟦ nothing ⟧
                                  (Π A B) → ⟦ just B ⟧) r

Π-inj₂ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂} → Π A₁ B₁ ≈T Π A₂ B₂ 
       → B₁ ≈T B₂
Π-inj₂ r = collapseΣ* (just-inj (πΠ₂≈ r))
