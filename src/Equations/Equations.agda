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
open import Equations.EqUtils
open import Equations.Coercions
open import Equations.Injectivity

module Equations.Equations where

≈T↑≈C : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ → Γ₁ ≈C Γ₂
≈t↑≈C : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} → M₁ ≈t M₂ → Γ₁ ≈C Γ₂
≈t↑≈T : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} → M₁ ≈t M₂ → A₁ ≈T A₂
≈s↑≈C₁ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂} → δ₁ ≈s δ₂ → Γ₁ ≈C Γ₂
≈s↑≈C₂ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂} → δ₁ ≈s δ₂ → Δ₁ ≈C Δ₂

_rfl[_]T≈ : ∀ {Γ Δ₁ Δ₂} A {δ₁ : Sub Δ₁ Γ} {δ₂ : Sub Δ₂ Γ}
          → δ₁ ≈s δ₂ → A [ δ₁ ]T ≋T A [ δ₂ ]T
_[_]T≈ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂} {δ₁ : Sub Δ₁ Γ₁} {δ₂ : Sub Δ₂ Γ₂}
       → A₁ ≈T A₂ → δ₁ ≈s δ₂ → A₁ [ δ₁ ]T ≈T A₂ [ δ₂ ]T

_rfl[_]T≈′_ : ∀ {Γ Δ₁ Δ₂} A {δ₁ : Sub Δ₁ Γ} {δ₂ : Sub Δ₂ Γ}
            → δ₁ ≈s δ₂ → Δ₁ ≈C Δ₂ → A [ δ₁ ]T ≋T A [ δ₂ ]T
U rfl[ δ ]T≈′ p = U p
El M rfl[ δ ]T≈′ p = El ⟦ rfl [ δ ]≋ ⟧
Π A B rfl[ δ ]T≈′ p = Π A[] ⟦ B rfl[ ⟦ δ ↑ rfl ⟧ ]T≈′ ⟦ p , A[] ⟧ ⟧
  where A[] = ⟦ A rfl[ δ ]T≈′ p ⟧

_[_]T≈′_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂} {δ₁ : Sub Δ₁ Γ₁} {δ₂ : Sub Δ₂ Γ₂}
         → A₁ ≈T A₂ → δ₁ ≈s δ₂ → Δ₁ ≈C Δ₂ → A₁ [ δ₁ ]T ≈T A₂ [ δ₂ ]T
rfl {x = A} [ δ ]T≈′ p = ⟦ A rfl[ δ ]T≈′ p ⟧
trs (U Γ  ¹) A [ δ ]T≈′ p = A [ sym (coh-s₂ (sym Γ)) ∙ δ ]T≈′ p
trs (U Γ ⁻¹) A [ δ ]T≈′ p = A [ sym (coh-s₂ Γ) ∙ δ ]T≈′ p
trs (El M ¹) A [ δ ]T≈′ p 
  = ⟦ El ⟦ M [ δ ∙ coh-s₂ (sym (≈t↑≈C M) ∙ ≈s↑≈C₂ δ) ]≋ ⟧ ⟧ 
  ∙ A [ sym (coh-s₂ (sym (≈t↑≈C M) ∙ ≈s↑≈C₂ δ)) ]T≈′ rfl
trs (El M ⁻¹) A [ δ ]T≈′ p 
  = ⟦ El ⟦ sym M [ δ ∙ coh-s₂ (≈t↑≈C M ∙ ≈s↑≈C₂ δ) ]≋ ⟧ ⟧ 
  ∙ A [ sym (coh-s₂ (≈t↑≈C M ∙ ≈s↑≈C₂ δ)) ]T≈′ rfl
trs (Π A B ¹) C [ δ ]T≈′ p 
  = ⟦ Π A[] (B [ ⟦ (δ ∙ coh-s₂ (sym (≈T↑≈C A) ∙ ≈s↑≈C₂ δ)) ↑ A ⟧ ]T≈′ 
               ⟦ p , A[] ⟧) ⟧ 
  ∙ C [ sym (coh-s₂ (sym (≈T↑≈C A) ∙ ≈s↑≈C₂ δ)) ]T≈′ rfl
  where A[] = A [ δ ∙ coh-s₂ (sym (≈T↑≈C A) ∙ ≈s↑≈C₂ δ) ]T≈′ p
trs (Π A B ⁻¹) C [ δ ]T≈′ p
  = ⟦ Π A[] (sym (B [ ⟦ (δ ∙ coh-s₂ (≈T↑≈C A ∙ ≈s↑≈C₂ δ)) ↑ sym A ⟧⁻¹ ]T≈′ 
                    ⟦ p , A[] ⟧⁻¹)) ⟧
  ∙ C [ sym (coh-s₂ (≈T↑≈C A ∙ ≈s↑≈C₂ δ)) ]T≈′ rfl
  where A[] = sym (A [ sym (δ ∙ coh-s₂ (≈T↑≈C A ∙ ≈s↑≈C₂ δ)) ]T≈′ sym p)

A rfl[ δ ]T≈ = A rfl[ δ ]T≈′ ≈s↑≈C₁ δ
A [ δ ]T≈ = A [ δ ]T≈′ ≈s↑≈C₁ δ

_↑↑rfl≈_ : ∀ {Γ₁ Γ₂ Δ} {δ₁ : Sub Γ₁ Δ} {δ₂ : Sub Γ₂ Δ} → δ₁ ≈s δ₂ → ∀ Σ 
      → δ₁ ↑↑ Σ ≈s δ₂ ↑↑ Σ 
δ ↑↑rfl≈ ε = δ
δ ↑↑rfl≈ (Σ , A) = ⟦ (δ ↑↑rfl≈ Σ) ↑ rfl ⟧

_↑↑≈_ :  ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {Σ₁ Σ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂} 
      → δ₁ ≈s δ₂ → Σ₁ ≈Ts Σ₂ → δ₁ ↑↑ Σ₁ ≈s δ₂ ↑↑ Σ₂ 
δ ↑↑≈ rfl {x = Σ} = δ ↑↑rfl≈ Σ 
δ ↑↑≈ trs (ε Γ ¹) Σ = coh-s₂ (sym Γ) ∙ ((sym (coh-s₂ (sym Γ)) ∙ δ) ↑↑≈ Σ)
δ ↑↑≈ trs (ε Γ ⁻¹) Σ = coh-s₂ Γ ∙ ((sym (coh-s₂ Γ) ∙ δ) ↑↑≈ Σ)
δ ↑↑≈ trs (Σ , A ¹) Ξ 
  = ⟦ (coh-s₂ _ ↑↑≈ Σ) ↑ A ⟧ ∙ ((sym (coh-s₂ (sym (≈Ts↑≈C Σ))) ∙ δ) ↑↑≈ Ξ)
δ ↑↑≈ trs (Σ , A ⁻¹) Ξ 
  = ⟦ (sym (coh-s₂ _) ↑↑≈ Σ) ↑ A ⟧⁻¹ ∙ ((sym (coh-s₂ (≈Ts↑≈C Σ)) ∙ δ) ↑↑≈ Ξ)

_rfl[_]Ts≈ : ∀ {Γ Δ₁ Δ₂} Σ {δ₁ : Sub Δ₁ Γ} {δ₂ : Sub Δ₂ Γ}
           → δ₁ ≈s δ₂ → Σ [ δ₁ ]Ts ≋Ts Σ [ δ₂ ]Ts
ε rfl[ δ ]Ts≈ = ε (≈s↑≈C₁ δ)
(Σ , A) rfl[ δ ]Ts≈ = ⟦ Σ rfl[ δ ]Ts≈ ⟧ , ⟦ A rfl[ δ ↑↑rfl≈ Σ ]T≈ ⟧

_[_]Ts≈ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ Σ₁ Σ₂} {δ₁ : Sub Δ₁ Γ₁} {δ₂ : Sub Δ₂ Γ₂}
       → Σ₁ ≈Ts Σ₂ → δ₁ ≈s δ₂ → Σ₁ [ δ₁ ]Ts ≈Ts Σ₂ [ δ₂ ]Ts
rfl {x = Σ} [ δ ]Ts≈ = ⟦ Σ rfl[ δ ]Ts≈ ⟧
trs (ε Γ  ¹) Σ [ δ ]Ts≈ = Σ [ sym (coh-s₂ (sym Γ)) ∙ δ ]Ts≈
trs (ε Γ ⁻¹) Σ [ δ ]Ts≈ = Σ [ sym (coh-s₂ Γ) ∙ δ ]Ts≈
trs (Δ , A  ¹) Σ [ δ ]Ts≈
  = ⟦ Δ [ coh-s₂ _ ]Ts≈ , A [ coh-s₂ _ ↑↑≈ Δ ]T≈ ⟧ 
  ∙ Σ [ sym (coh-s₂ (sym (≈Ts↑≈C Δ))) ∙ δ ]Ts≈
trs (Δ , A ⁻¹) Σ [ δ ]Ts≈
  = ⟦ Δ [ sym (coh-s₂ _) ]Ts≈ , A [ sym (coh-s₂ _) ↑↑≈ Δ ]T≈ ⟧⁻¹
  ∙ Σ [ sym (coh-s₂ (≈Ts↑≈C Δ)) ∙ δ ]Ts≈

<>-commTs : ∀ {Γ Δ A N} (Σ : Tys (Γ , A)) (δ : Sub Δ Γ)
          → Σ [ δ ↑ A ]Ts [ < N [ δ ] > ]Ts
        ≈Ts Σ [ < N > ]Ts [ δ ]Ts
<>-commT′ : ∀ {Γ Δ A Σ N} (B : Ty (Γ , A ++ Σ)) (δ : Sub Δ Γ)
           → (p : Σ [ δ ↑ A ]Ts [ < N [ δ ] > ]Ts ≈Ts Σ [ < N > ]Ts [ δ ]Ts)
           → B [ (δ ↑ A) ↑↑ Σ ]T [ < N [ δ ] > ↑↑ (Σ [ δ ↑ A ]Ts) ]T
          ≋T B [ < N > ↑↑ Σ ]T [ δ ↑↑ (Σ [ < N > ]Ts) ]T
<>-commT : ∀ {Γ Δ A Σ N} (B : Ty (Γ , A ++ Σ)) (δ : Sub Δ Γ)
         → B [ (δ ↑ A) ↑↑ Σ ]T [ < N [ δ ] > ↑↑ (Σ [ δ ↑ A ]Ts) ]T
        ≋T B [ < N > ↑↑ Σ ]T [ δ ↑↑ (Σ [ < N > ]Ts) ]T

<>-commTs ε δ = rfl
<>-commTs (Σ , B) δ = ⟦ Σ<> , ⟦ <>-commT′ {Σ = Σ} B δ Σ<> ⟧ ⟧
  where Σ<> = <>-commTs Σ δ

<>-commT′ {Σ = Σ} U δ p = U (rfl ++≈ p)
<>-commT′ {Σ = Σ} (El M) δ _ = El ⟦ <>-comm {Σ = Σ} M δ ⟧
<>-commT′ {Σ = Σ} (Π B C) δ p
  = Π B<> ⟦ <>-commT′ {Σ = Σ , B} C δ ⟦ p , B<> ⟧ ⟧
  where B<> = ⟦ <>-commT′ B δ p ⟧

<>-commT {Σ = Σ} B δ = <>-commT′ {Σ = Σ} B δ (<>-commTs Σ δ)

wk-commTs : ∀ {Γ Δ A} (Σ : Tys Γ) (δ : Sub Δ Γ)
          → Σ [ wk ]Ts [ δ ↑ A ]Ts
        ≈Ts Σ [ δ ]Ts [ wk {A = A [ δ ]T} ]Ts
wk-commT : ∀ {Γ Δ A Σ} (B : Ty (Γ ++ Σ)) (δ : Sub Δ Γ)
         → B [ wk ↑↑ Σ ]T [ (δ ↑ A) ↑↑ (Σ [ wk ]Ts) ]T
        ≋T B [ δ ↑↑ Σ ]T [ wk {A = A [ δ ]T} ↑↑ (Σ [ δ ]Ts) ]T
wk-commT′ : ∀ {Γ Δ A Σ} (B : Ty (Γ ++ Σ)) (δ : Sub Δ Γ)
          → Σ [ wk ]Ts [ δ ↑ A ]Ts
        ≈Ts Σ [ δ ]Ts [ wk {A = A [ δ ]T} ]Ts
          → B [ wk ↑↑ Σ ]T [ (δ ↑ A) ↑↑ (Σ [ wk ]Ts) ]T
         ≋T B [ δ ↑↑ Σ ]T [ wk {A = A [ δ ]T} ↑↑ (Σ [ δ ]Ts) ]T

wk-commT′ U δ Σ = U (rfl ++≈ Σ)
wk-commT′ (El M) δ Σ = El ⟦ wk-comm M δ ⟧
wk-commT′ (Π A B) δ Σ = Π Awk ⟦ wk-commT′ B δ ⟦ Σ , Awk ⟧ ⟧
  where Awk = ⟦ wk-commT′ A δ Σ ⟧

wk-commTs ε δ = rfl
wk-commTs (Σ , A) δ = ⟦ Σwk , ⟦ wk-commT′ {Σ = Σ} A δ Σwk ⟧ ⟧
  where Σwk = wk-commTs Σ δ

wk-commT {Σ = Σ} A δ = wk-commT′ A δ (wk-commTs Σ _)

wk-vz-idTs : ∀ {Γ B} (Δ : Tys (Γ , B)) 
           → Δ [ wk ↑ B ]Ts [ < vz > ]Ts ≈Ts Δ
wk-vz-idT : ∀ {Γ B Δ} (A : Ty ((Γ , B) ++ Δ)) 
          → A [ (wk ↑ B) ↑↑ Δ ]T [ < vz > ↑↑ (Δ [ wk ↑ B ]Ts) ]T ≋T A
wk-vz-idT′ : ∀ {Γ B Δ} (A : Ty ((Γ , B) ++ Δ))
           → Δ [ wk ↑ B ]Ts [ < vz > ]Ts ≈Ts Δ
           → A [ (wk ↑ B) ↑↑ Δ ]T [ < vz > ↑↑ (Δ [ wk ↑ B ]Ts) ]T ≋T A

wk-vz-idT′ U Δ       = U (rfl ++≈ Δ)
wk-vz-idT′ (El M) Δ  = El ⟦ wk-vz-id M ⟧
wk-vz-idT′ (Π A B) Δ = Π Awkvz ⟦ wk-vz-idT′ B ⟦ Δ , Awkvz ⟧ ⟧
  where Awkvz = ⟦ wk-vz-idT′ A Δ ⟧

wk-vz-idTs ε       = rfl
wk-vz-idTs (Δ , A) = ⟦ wk-vz-idTs Δ , ⟦ wk-vz-idT′ A Δwkvz ⟧ ⟧
  where Δwkvz = wk-vz-idTs Δ

wk-vz-idT A = wk-vz-idT′ A (wk-vz-idTs _)

wk-<>-idTs : ∀ {Γ B} (Δ : Tys Γ) {N : Tm Γ B} 
           → Δ [ wk ]Ts [ < N > ]Ts ≈Ts Δ
wk-<>-idT : ∀ {Γ Δ B} (A : Ty (Γ ++ Δ)) {N : Tm Γ B} 
          → A [ wk ↑↑ Δ ]T [ < N > ↑↑ (Δ [ wk ]Ts) ]T ≋T A
wk-<>-idT′ : ∀ {Γ Δ B} (A : Ty (Γ ++ Δ)) {N : Tm Γ B} 
           → Δ [ wk ]Ts [ < N > ]Ts ≈Ts Δ
           → A [ wk ↑↑ Δ ]T [ < N > ↑↑ (Δ [ wk ]Ts) ]T ≋T A

wk-<>-idT′ U       Δ = U (rfl ++≈ Δ)
wk-<>-idT′ (El M)  Δ = El ⟦ wk-<>-id M ⟧
wk-<>-idT′ (Π A B) Δ = Π Awk<> ⟦ wk-<>-idT′ B ⟦ Δ , Awk<> ⟧ ⟧
  where Awk<> = ⟦ wk-<>-idT′ A Δ ⟧

wk-<>-idTs ε       = rfl
wk-<>-idTs (Δ , A) = ⟦ Δwk<> , ⟦ wk-<>-idT′ A Δwk<> ⟧ ⟧
  where Δwk<> = wk-<>-idTs Δ

wk-<>-idT A = wk-<>-idT′ A (wk-<>-idTs _)

≋T↑≈C : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≋T A₂ → Γ₁ ≈C Γ₂
≋T↑≈C (U Γ)   = Γ
≋T↑≈C (El M)  = ≈t↑≈C M
≋T↑≈C (Π A B) = ≈T↑≈C A

↭T↑≈C : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ↭T A₂ → Γ₁ ≈C Γ₂
↭T↑≈C (A ¹) = ≋T↑≈C A
↭T↑≈C (A ⁻¹) = sym (≋T↑≈C A)

-- Ideally we would just lift ≋T↑≈C, but this becomes opaque to the termination 
-- checker
-- ≈T↑≈C r = lift-proof (λ {Γ} _ → Γ) ≋T↑≈C r
≈T↑≈C rfl       = rfl
≈T↑≈C (trs A r) = ↭T↑≈C A ∙ ≈T↑≈C r

≋t↑≈C : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} → M₁ ≋t M₂ → Γ₁ ≈C Γ₂
≋t↑≈C (coh A) = sym (↭T↑≈C A)
≋t↑≈C (lam M) = ,-inj₁ (≈t↑≈C M)
≋t↑≈C (app M N) = ≈t↑≈C M
≋t↑≈C (vz A) = ⟦ ≈T↑≈C A , A ⟧
≋t↑≈C (M [ δ ]≋) = ≈s↑≈C₁ δ
≋t↑≈C β = rfl
≋t↑≈C η = rfl
≋t↑≈C (wk-vz-id _) = rfl ++≈ wk-vz-idTs _
≋t↑≈C (wk-<>-id {Δ = Δ} _) = rfl ++≈ wk-<>-idTs Δ
≋t↑≈C (<>-comm {Σ = Σ} M δ) = rfl ++≈ <>-commTs Σ δ
≋t↑≈C (wk-comm {Σ = Σ} M δ) = rfl ++≈ wk-commTs Σ δ
≋t↑≈C vz<> = rfl
≋t↑≈C vz[] = rfl
≋t↑≈C lam[] = rfl
≋t↑≈C app[] = rfl

≈t↑≈C rfl = rfl
≈t↑≈C (trs (M ¹) r) = ≋t↑≈C M ∙ ≈t↑≈C r
≈t↑≈C (trs (M ⁻¹) r) = sym (≋t↑≈C M) ∙ ≈t↑≈C r

≋t↑≈T : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} → M₁ ≋t M₂ → A₁ ≈T A₂
≋t↑≈T (coh A) = trs (symsym A) rfl
≋t↑≈T (lam M) = ⟦ Π (,-inj₂ (≈t↑≈C M)) (≈t↑≈T M) ⟧
≋t↑≈T (app M N) = Π-inj₂ (≈t↑≈T M) [ ⟦ [ ≈t↑≈C M , ≈t↑≈T N ]< N > ⟧ ]T≈
≋t↑≈T (vz A) = A [ ⟦ wk (≈T↑≈C A) A ⟧ ]T≈
≋t↑≈T (M [ δ ]≋) = ≈t↑≈T M [ δ ]T≈
≋t↑≈T β = rfl
≋t↑≈T η = ⟦ Π rfl ⟦ wk-vz-idT _ ⟧ ⟧
≋t↑≈T (wk-vz-id _) = ⟦ wk-vz-idT _ ⟧
≋t↑≈T (wk-<>-id _) = ⟦ wk-<>-idT _ ⟧
≋t↑≈T (<>-comm {B = B} M δ) = ⟦ <>-commT B δ ⟧
≋t↑≈T (wk-comm {A = A} M δ) = ⟦ wk-commT A δ ⟧
≋t↑≈T vz<> = ⟦ wk-<>-idT _ ⟧
≋t↑≈T vz[] = ⟦ wk-commT _ _ ⟧
≋t↑≈T lam[] = rfl
≋t↑≈T app[] = ⟦ <>-commT _ _ ⟧⁻¹

≈t↑≈T rfl = rfl
≈t↑≈T (trs (M  ¹) r) = ≋t↑≈T M ∙ ≈t↑≈T r
≈t↑≈T (trs (M ⁻¹) r) = sym (≋t↑≈T M) ∙ ≈t↑≈T r

≋s↑≈C₁ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂} 
        → δ₁ ≋s δ₂ → Γ₁ ≈C Γ₂
≋s↑≈C₁ (coh₁ Γ) = trs (symsym Γ) rfl
≋s↑≈C₁ (coh₂ Δ) = rfl
≋s↑≈C₁ (wk Γ A) = ⟦ Γ , A ⟧
≋s↑≈C₁ [ Γ , A ]< M > = Γ
≋s↑≈C₁ (δ ↑ A) = ⟦ Γ , A [ δ ]T≈′ Γ ⟧
  where Γ = ≈s↑≈C₁ δ

≋s↑≈C₂ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂} 
        → δ₁ ≋s δ₂ → Δ₁ ≈C Δ₂
≋s↑≈C₂ (coh₁ Γ) = rfl
≋s↑≈C₂ (coh₂ Δ) = trs (symsym Δ) rfl
≋s↑≈C₂ (wk Γ δ) = Γ
≋s↑≈C₂ [ Γ , A ]< M > = ⟦ Γ , A ⟧
≋s↑≈C₂ (δ ↑ A) = ⟦ ≈s↑≈C₂ δ , A ⟧

≈s↑≈C₁ rfl = rfl
≈s↑≈C₁ (trs (δ  ¹) r) = ≋s↑≈C₁ δ ∙ ≈s↑≈C₁ r
≈s↑≈C₁ (trs (δ ⁻¹) r) = sym (≋s↑≈C₁ δ) ∙ ≈s↑≈C₁ r

≈s↑≈C₂ rfl = rfl
≈s↑≈C₂ (trs (δ  ¹) r) = ≋s↑≈C₂ δ ∙ ≈s↑≈C₂ r
≈s↑≈C₂ (trs (δ ⁻¹) r) = sym (≋s↑≈C₂ δ) ∙ ≈s↑≈C₂ r

<_>≈ : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} 
     → M₁ ≈t M₂ → < M₁ > ≋s < M₂ >
< M >≈ = [ ≈t↑≈C M , ≈t↑≈T M ]< M >

wk≈ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ 
      → wk {A = A₁} ≋s wk {A = A₂}
wk≈ A = wk (≈T↑≈C A) A
