{-# OPTIONS --without-K #-}
-- {-# OPTIONS --lossy-unification #-}

open import Level using (suc)
open import Data.Product using (∃) renaming (_,_ to infixl 6 _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; refl)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥-elim; ⊥)
open import Function.Base using (id; _∘_; _∋_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing; map) 

open import Syntax
open import EqUtils

module Equations where

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

coe-T : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → Ty Γ₁ → Ty Γ₂
coe-T rfl A = A
coe-T (trs p q) A = coe p (coe-T q A)

coh-T : ∀ {Γ₁ Γ₂} (Γ : Γ₁ ≈C Γ₂) {A : Ty Γ₁} → coe-T Γ A ≈T A
coh-T rfl = rfl
coh-T (trs p r) = coh-T r ∙ ⟦ _≋T_.coh p ⟧

coe-T≈ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} (p : Γ₁ ≈C Γ₂) (q : Δ₁ ≈C Δ₂) {A₁ A₂}
       → A₁ ≈T A₂ → coe-T p A₁ ≈T coe-T q A₂
coe-T≈ rfl q A = sym (coh-T q)  ∙ A
coe-T≈ (trs p r) q A = coe-T≈ r q A ∙ ⟦ coh p ⟧

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

U-diverge : ∀ {Γ} → Ty Γ → Set
U-diverge (coe _ A) = U-diverge A
U-diverge U = ⊥
U-diverge (El M) = ⊤
U-diverge (Π A B) = ⊤

Π-diverge : ∀ {Γ} → Ty Γ → Set
Π-diverge (coe _ A) = Π-diverge A
Π-diverge U = ⊤
Π-diverge (El _) = ⊤
Π-diverge (Π _ _) = ⊥

U-diverge≈ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} 
                  → A₁ ≈T A₂ → U-diverge A₁ ≡ U-diverge A₂
U-diverge≈ rfl = refl
U-diverge≈ (trs (coh _  ¹) r) = U-diverge≈ r
U-diverge≈ (trs (U _    ¹) r) = U-diverge≈ r
U-diverge≈ (trs (El _   ¹) r) = U-diverge≈ r
U-diverge≈ (trs (Π _ _  ¹) r) = U-diverge≈ r
U-diverge≈ (trs (coh _ ⁻¹) r) = U-diverge≈ r
U-diverge≈ (trs (U _   ⁻¹) r) = U-diverge≈ r
U-diverge≈ (trs (El _  ⁻¹) r) = U-diverge≈ r
U-diverge≈ (trs (Π _ _ ⁻¹) r) = U-diverge≈ r

U-El-disj : ∀ {Γ₁ Γ₂} {M : Tm Γ₂ U} → ¬ El M ≈T U {Γ₁}
U-El-disj p = subst id (U-diverge≈ p) tt

πEl : ∀ {Γ} → Ty Γ → Maybe (Tm Γ U)
πEl (coe p A) = map (coe (U (trs p rfl) ¹)) (πEl A)
πEl U = nothing
πEl (El A) = just A
πEl (Π _ _) = nothing

πEl≈ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ 
     → πEl A₁ ≈Maybe[ *SymClosure _≋t_ ] πEl A₂
πEl≈ r = lift-proof πEl (λ where (coh p) → ⟦ mapInv ⟦ coh _ ⟧ ⟧
                                 (U _)   → ⟦ nothing ⟧
                                 (El M)  → ⟦ just M ⟧
                                 (Π _ _) → ⟦ nothing ⟧) r

El-inj : ∀ {Γ₁ Γ₂} {M₁ : Tm Γ₁ U} {M₂ : Tm Γ₂ U} → El M₁ ≈T El M₂ → M₁ ≈t M₂
El-inj r = collapse* (just-inj (πEl≈ r))

πΠ₁ : ∀ {Γ} → Ty Γ → Maybe (Ty Γ)
πΠ₁ (coe p A) = map (coe p) (πΠ₁ A)
πΠ₁ U         = nothing
πΠ₁ (El M)    = nothing
πΠ₁ (Π A B)   = just A

πΠ≈₁ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ 
     → πΠ₁ A₁ ≈Maybe[ *SymClosure _≋T_ ] πΠ₁ A₂
πΠ≈₁ r = lift-proof πΠ₁ (λ where (coh p) → ⟦ mapInv ⟦ coh _ ⟧ ⟧
                                 (U _)   → ⟦ nothing ⟧
                                 (El M)  → ⟦ nothing ⟧
                                 (Π A _) → ⟦ just A ⟧) r

Π-inj₁ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂} → Π A₁ B₁ ≈T Π A₂ B₂
       → A₁ ≈T A₂
Π-inj₁ r = collapse* (just-inj (πΠ≈₁ r))

∃πΠ₂ : ∀ {Γ} → Ty Γ → Maybe (∃ Ty)
∃πΠ₂ (coe _ A) = ∃πΠ₂ A
∃πΠ₂ U = nothing
∃πΠ₂ (El _) = nothing
∃πΠ₂ (Π A B) = just (_ , B)

πΠ₂≈ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂  
     → ∃πΠ₂ A₁ ≈Maybe[ _≋Σ[ _≈T_ ]_ ] ∃πΠ₂ A₂
πΠ₂≈ r = lift-proof ∃πΠ₂ (λ where (coh p) → rfl
                                  (U _) → ⟦ nothing ⟧
                                  (El _) → ⟦ nothing ⟧
                                  (Π A B) → ⟦ just B ⟧) r

Π-inj₂ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂} → Π A₁ B₁ ≈T Π A₂ B₂ 
       → B₁ ≈T B₂
Π-inj₂ r = collapseΣ* (just-inj (πΠ₂≈ r))

-- Reached here with no holes!

-- Andras Kovacs makes these projections constructors
-- I would like to define these recursively (so proofs don't have to handle
-- these as cases) but it might turn out to be impossible. We shall see...
≈T↑≈C : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ → Γ₁ ≈C Γ₂
≈Ts↑≈C : ∀ {Γ₁ Γ₂} {Δ₁ : Tys Γ₁} {Δ₂ : Tys Γ₂} → Δ₁ ≈Ts Δ₂ → Γ₁ ≈C Γ₂
≈t↑≈C : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} → M₁ ≈t M₂ → Γ₁ ≈C Γ₂
≈s↑≈C₁ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂} → δ₁ ≈s δ₂ → Γ₁ ≈C Γ₂
≈s↑≈C₂ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂} → δ₁ ≈s δ₂ → Δ₁ ≈C Δ₂

_++≈_ : ∀ {Γ₁ Γ₂} {Δ₁ : Tys Γ₁} {Δ₂ : Tys Γ₂}
    → Γ₁ ≈C Γ₂ → Δ₁ ≈Ts Δ₂ → Γ₁ ++ Δ₁ ≈C Γ₂ ++ Δ₂

_rfl[_]T≈ : ∀ {Γ Δ₁ Δ₂} A {δ₁ : Sub Δ₁ Γ} {δ₂ : Sub Δ₂ Γ}
          → δ₁ ≈s δ₂ → A [ δ₁ ]T ≋T A [ δ₂ ]T
coe p A rfl[ δ ]T≈ = A rfl[ ⟦ coh₂ (symsym p) ⟧⁻¹ ∙ δ ∙ ⟦ coh₂ (symsym p) ⟧ ]T≈
U rfl[ δ ]T≈ = U (≈s↑≈C₁ δ)
El M rfl[ δ ]T≈ = El ⟦ rfl [ δ ]≋ ⟧
Π A B rfl[ δ ]T≈ = Π ⟦ A rfl[ δ ]T≈ ⟧ ⟦ B rfl[ ⟦ δ ↑ rfl ⟧ ]T≈ ⟧

_[_]T≈ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂} {δ₁ : Sub Δ₁ Γ₁} {δ₂ : Sub Δ₂ Γ₂}
       → A₁ ≈T A₂ → δ₁ ≈s δ₂ → A₁ [ δ₁ ]T ≈T A₂ [ δ₂ ]T
rfl {x = A} [ δ ]T≈ = ⟦ A rfl[ δ ]T≈ ⟧
trs (coh {A = A′} p ¹) A [ δ ]T≈ 
  = ⟦ A′ rfl[ ⟦ coh₂ p ⟧ ∙ ⟦ coh₂ (symsym p) ⟧ ]T≈ ⟧ ∙ A [ ⟦ coh₂ p ⟧⁻¹ ∙ δ ]T≈
trs (coh {A = A′} p ⁻¹) A [ δ ]T≈ 
  = ⟦ A′ rfl[ ⟦ coh₂ p ⟧ ∙ ⟦ coh₂ p ⟧⁻¹ ]T≈ ⟧
 ∙ A [ ⟦ coh₂ (symsym p) ⟧⁻¹ ∙ δ ]T≈
trs (U Γ  ¹) A [ δ ]T≈ = A [ sym (coh-s₂ (sym Γ)) ∙ δ ]T≈
trs (U Γ ⁻¹) A [ δ ]T≈ = A [ sym (coh-s₂ Γ) ∙ δ ]T≈
trs (El M ¹) A [ δ ]T≈ 
  = ⟦ El ⟦ M [ δ ∙ coh-s₂ (sym (≈t↑≈C M) ∙ ≈s↑≈C₂ δ) ]≋ ⟧ ⟧ 
  ∙ A [ sym (coh-s₂ _) ]T≈
trs (El M ⁻¹) A [ δ ]T≈ 
  = ⟦ El ⟦ sym M [ δ ∙ coh-s₂ (≈t↑≈C M ∙ ≈s↑≈C₂ δ) ]≋ ⟧ ⟧ 
  ∙ A [ sym (coh-s₂ _) ]T≈
trs (Π A B ¹) C [ δ ]T≈ 
  = ⟦ Π (A [ δ ∙ coh-s₂ (sym (≈T↑≈C A) ∙ ≈s↑≈C₂ δ) ]T≈) 
        (B [ ⟦ (δ ∙ coh-s₂ _) ↑ A ⟧ ]T≈) ⟧ 
  ∙ C [ sym (coh-s₂ _) ]T≈
trs (Π A B ⁻¹) C [ δ ]T≈
  = ⟦ Π (sym (A [ sym (δ ∙ coh-s₂ (≈T↑≈C A ∙ ≈s↑≈C₂ δ)) ]T≈))
        (sym (B [ ⟦ (δ ∙ coh-s₂ _) ↑ sym A ⟧⁻¹ ]T≈)) ⟧
  ∙ C [ sym (coh-s₂ _) ]T≈

_↑↑rfl≈_ : ∀ {Γ₁ Γ₂ Δ} {δ₁ : Sub Γ₁ Δ} {δ₂ : Sub Γ₂ Δ} → δ₁ ≈s δ₂ → ∀ Σ 
      → δ₁ ↑↑ Σ ≈s δ₂ ↑↑ Σ 
δ ↑↑rfl≈ coe x Σ  = (⟦ coh₂ _ ⟧⁻¹ ∙ δ ∙ ⟦ coh₂ _ ⟧) ↑↑rfl≈ Σ
δ ↑↑rfl≈ ε = δ
δ ↑↑rfl≈ (Σ , A) = ⟦ (δ ↑↑rfl≈ Σ) ↑ rfl ⟧

_↑↑≈_ :  ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {Σ₁ Σ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂} 
      → δ₁ ≈s δ₂ → Σ₁ ≈Ts Σ₂ → δ₁ ↑↑ Σ₁ ≈s δ₂ ↑↑ Σ₂ 
δ ↑↑≈ rfl {x = Σ} = δ ↑↑rfl≈ Σ 
δ ↑↑≈ trs (coh {Δ = Σ′} p ¹) Σ 
  = ((⟦ coh₂ _ ⟧ ∙ ⟦ coh₂ _ ⟧) ↑↑rfl≈ Σ′) ∙ ((⟦ coh₂ p ⟧⁻¹ ∙ δ) ↑↑≈ Σ)
δ ↑↑≈ trs (coh {Δ = Σ′} p ⁻¹) Σ 
  = ((⟦ coh₂ _ ⟧⁻¹ ∙ ⟦ coh₂ (symsym p) ⟧) ↑↑rfl≈ Σ′) 
  ∙ ((⟦ coh₂ _ ⟧⁻¹ ∙ δ) ↑↑≈ Σ)
δ ↑↑≈ trs (ε Γ ¹) Σ = coh-s₂ (sym Γ) ∙ ((sym (coh-s₂ (sym Γ)) ∙ δ) ↑↑≈ Σ)
δ ↑↑≈ trs (ε Γ ⁻¹) Σ = coh-s₂ Γ ∙ ((sym (coh-s₂ Γ) ∙ δ) ↑↑≈ Σ)
δ ↑↑≈ trs (Σ , A ¹) Ξ 
  = ⟦ (coh-s₂ _ ↑↑≈ Σ) ↑ A ⟧ ∙ ((sym (coh-s₂ (sym (≈Ts↑≈C Σ))) ∙ δ) ↑↑≈ Ξ)
δ ↑↑≈ trs (Σ , A ⁻¹) Ξ 
  = ⟦ (sym (coh-s₂ _) ↑↑≈ Σ) ↑ A ⟧⁻¹ ∙ ((sym (coh-s₂ (≈Ts↑≈C Σ)) ∙ δ) ↑↑≈ Ξ)

_rfl[_]Ts≈ : ∀ {Γ Δ₁ Δ₂} Σ {δ₁ : Sub Δ₁ Γ} {δ₂ : Sub Δ₂ Γ}
           → δ₁ ≈s δ₂ → Σ [ δ₁ ]Ts ≋Ts Σ [ δ₂ ]Ts
coe p Σ rfl[ δ ]Ts≈ = Σ rfl[ ⟦ coh₂ _ ⟧⁻¹ ∙ δ ∙ ⟦ coh₂ _ ⟧  ]Ts≈
ε rfl[ δ ]Ts≈ = ε (≈s↑≈C₁ δ)
(Σ , A) rfl[ δ ]Ts≈ = ⟦ Σ rfl[ δ ]Ts≈ ⟧ , ⟦ A rfl[ δ ↑↑rfl≈ Σ ]T≈ ⟧

_[_]Ts≈ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ Σ₁ Σ₂} {δ₁ : Sub Δ₁ Γ₁} {δ₂ : Sub Δ₂ Γ₂}
       → Σ₁ ≈Ts Σ₂ → δ₁ ≈s δ₂ → Σ₁ [ δ₁ ]Ts ≈Ts Σ₂ [ δ₂ ]Ts
rfl {x = Σ} [ δ ]Ts≈ = ⟦ Σ rfl[ δ ]Ts≈ ⟧
trs (coh {Δ = Δ} p ¹) Σ [ δ ]Ts≈ 
  = ⟦ Δ rfl[ ⟦ coh₂ _ ⟧ ∙ ⟦ coh₂ _ ⟧ ]Ts≈ ⟧ ∙ Σ [ ⟦ coh₂ p ⟧⁻¹ ∙ δ ]Ts≈
trs (coh {Δ = Δ} p ⁻¹) Σ [ δ ]Ts≈ 
  = ⟦ Δ rfl[ ⟦ coh₂ p ⟧ ∙ ⟦ coh₂ _ ⟧⁻¹ ]Ts≈ ⟧ ∙ Σ [ ⟦ coh₂ _ ⟧⁻¹ ∙ δ ]Ts≈
trs (ε Γ  ¹) Σ [ δ ]Ts≈ = Σ [ sym (coh-s₂ (sym Γ)) ∙ δ ]Ts≈
trs (ε Γ ⁻¹) Σ [ δ ]Ts≈ = Σ [ sym (coh-s₂ Γ) ∙ δ ]Ts≈
trs (Δ , A  ¹) Σ [ δ ]Ts≈
  = ⟦ Δ [ coh-s₂ _ ]Ts≈ , A [ coh-s₂ _ ↑↑≈ Δ ]T≈ ⟧ 
  ∙ Σ [ sym (coh-s₂ (sym (≈Ts↑≈C Δ))) ∙ δ ]Ts≈
trs (Δ , A ⁻¹) Σ [ δ ]Ts≈
  = ⟦ Δ [ sym (coh-s₂ _) ]Ts≈ , A [ sym (coh-s₂ _) ↑↑≈ Δ ]T≈ ⟧⁻¹
  ∙ Σ [ sym (coh-s₂ (≈Ts↑≈C Δ)) ∙ δ ]Ts≈

-- <>-comm-subTs : ∀ {Γ Δ A N} (Σ : Tys (Γ , A)) (δ : Sub Δ Γ)
--               → Σ [ δ ↑ A ]Ts [ < N [ δ ] > ]Ts
--             ≈Ts Σ [ < N > ]Ts [ δ ]Ts
-- <>-comm-subT[] : ∀ {Γ Δ A Σ N} (B : Ty (Γ , A ++ Σ)) (δ : Sub Δ Γ)
--                → (p : Σ [ δ ↑ A ]Ts [ < N [ δ ] > ]Ts ≈Ts Σ [ < N > ]Ts [ δ ]Ts)
--                → B [ (δ ↑ A) ↑↑ Σ ]T [ < N [ δ ] > ↑↑ (Σ [ δ ↑ A ]Ts) ]T
--               ≈[ rfl ++≈ p ]T B [ < N > ↑↑ Σ ]T [ δ ↑↑ (Σ [ < N > ]Ts) ]T
-- <>-comm-subT : ∀ {Γ Δ A Σ N} (B : Ty (Γ , A ++ Σ)) (δ : Sub Δ Γ)
--              → B [ (δ ↑ A) ↑↑ Σ ]T [ < N [ δ ] > ↑↑ (Σ [ δ ↑ A ]Ts) ]T
--             ≈T B [ < N > ↑↑ Σ ]T [ δ ↑↑ (Σ [ < N > ]Ts) ]T

-- <>-comm-subTs (coe {Δ = ε} p Σ) δ = ⊥-elim (,ε-disj (trs (symsym p) rfl))
-- <>-comm-subTs {N = N} (coe {Δ = Ξ , B} p Σ) δ 
--   = ⟦ Σ rfl[ {!!} ]Ts≈ ⟧ [ {!!} ]Ts≈ 
--   ∙ <>-comm-subTs {N = {!coe (≈C-inj₂ p′!) N!}} Σ {!(coe rfl (≈C-inj₁ p′) δ)!}
--   ∙ ⟦ Σ rfl[ {!!} ]Ts≈ ⟧ [ {!!} ]Ts≈
--   where 
--     p′ = symsym p
--     coh1 : coe₂ p′ (δ ↑ _) ≈s coe₂ (≈C-inj₁ p′) δ ↑ B
--     coh1 = ⟦ coh₂ p′ ⟧ ∙ ⟦ ⟦ coh₂ (≈C-inj₁ p′) ⟧⁻¹ ↑ ≈C-inj₂ p′ ⟧
--     coh2 : < N [ δ ] > ≈s < coe (≈C-inj₂ p′) N [ coe₂ (≈C-inj₁ p′) δ ] >
--     coh2 = ⟦ < ⟦ ⟦ coh (≈C-inj₂ p′) ⟧⁻¹ [ ⟦ coh₂ (≈C-inj₁ p′) ⟧⁻¹ ]≋ ⟧ > ⟧
--     coh3 : < coe (≈C-inj₂ p′) N > ≈s coe₂ p′ < N >
--     coh3 = ⟦ < ⟦ coh (≈C-inj₂ p′) ⟧ > ⟧ ∙ ⟦ coh₂ p′ ⟧⁻¹
--     coh4 : coe₂ (≈C-inj₁ p′) δ ≈s δ
--     coh4 = ⟦ coh₂ (≈C-inj₁ p′) ⟧

-- <>-comm-subTs ε δ = rfl
-- <>-comm-subTs (Σ , B) δ 
--   = ⟦ Σδ , <>-comm-subT[] {Σ = Σ} B δ Σδ ⟧
--   where
--     Σδ = <>-comm-subTs Σ δ

-- -- Oh god I don't want to have to prove a billion coherences again
-- <>-comm-subT[] (coe x B) δ _ = {!   !}

-- <>-comm-subT[] {Σ = Σ} U δ p = ⟦ U (rfl ++≈ p) ⟧
-- <>-comm-subT[] {Σ = Σ} (El M) δ _ = ⟦ El ⟦ <>-comm-sub {Σ = Σ} M δ ⟧ ⟧
-- <>-comm-subT[] {Σ = Σ} (Π B C) δ p
--   = ⟦ Π (<>-comm-subT[] {Σ = Σ , B} C δ ⟦ p , <>-comm-subT[] {Σ = Σ} B δ p ⟧) ⟧
  
-- <>-comm-subT {Σ = Σ} B δ = <>-comm-subT[] {Σ = Σ} B δ (<>-comm-subTs Σ δ)

-- ≋T↑≈C : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≋T A₂ → Γ₁ ≈C Γ₂
-- ≋T↑≈C (coh p) = sym p
-- ≋T↑≈C (U Γ)   = Γ
-- ≋T↑≈C (El M)  = ≈t↑≈C M
-- ≋T↑≈C (Π B)   = {!!}

-- ≈T↑≈C = lift-proof IsTy (λ where prf prf refl → refl) (λ where 
--           (x  ¹) prf → ≋T→IsTy₂ x
--           (x ⁻¹) prf → ≋T→IsTy₁ x
--         ) {C = λ _ _ → ctx} (λ where _ (prf {Γ}) → Γ) (λ where prf prf → ≋T↑≈C) 
--         prf prf

-- ≋t↑≈C : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} → M₁ ≋t M₂ → Γ₁ ≈C Γ₂
-- ≋t↑≈C (coh A) = sym (≈T↑≈C A)
-- ≋t↑≈C (lam M) = ≈C-inj₁ (≈t↑≈C M)
-- ≋t↑≈C (app M N) = rfl
-- ≋t↑≈C (vz A) = ⟦ ≈T↑≈C A , A ⟧
-- ≋t↑≈C (M [ δ ]≋) = {!!}
-- ≋t↑≈C β = rfl
-- ≋t↑≈C η = rfl
-- ≋t↑≈C (<>-comm-sub {Σ = Σ} M δ) = rfl ++≈ <>-comm-subTs Σ δ

-- ≈t↑≈C p = lift-proof IsTm (λ where prf prf refl → refl) (λ where 
--             (x  ¹) prf → ≋t→IsTm₂ x
--             (x ⁻¹) prf → ≋t→IsTm₁ x
--           ) {C = λ _ _ → ctx}
--           (λ where _ (prf {Γ}) → Γ) (λ where prf prf → ≋t↑≈C) prf prf p

Γ ++≈ rfl = rfl
Γ ++≈ trs (coh p  ¹) r = (trs p rfl ∙ Γ) ++≈ r
Γ ++≈ trs (coh p ⁻¹) r = (trs (symsym p) rfl ∙ Γ) ++≈ r
Γ ++≈ trs (ε Σ    ¹) Δ = Σ ∙ ((sym Σ ∙ Γ) ++≈ Δ) 
Γ ++≈ trs (ε Σ   ⁻¹) Δ = sym Σ ∙ ((Σ ∙ Γ) ++≈ Δ)
Γ ++≈ trs (Δ , A  ¹) p = ⟦ (≈Ts↑≈C Δ ++≈ Δ) , A ⟧ ∙ ((sym (≈Ts↑≈C Δ) ∙ Γ) ++≈ p)
Γ ++≈ trs (Δ , A ⁻¹) p = sym ⟦ (≈Ts↑≈C Δ ++≈ Δ) ,  A ⟧ ∙ ((≈Ts↑≈C Δ ∙ Γ) ++≈ p)
  