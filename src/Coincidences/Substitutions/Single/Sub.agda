{-# OPTIONS --rewriting --prop #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys
open import Coincidences.Substitutions.Common
open import Coincidences.Substitutions.Single.Weak

-- Todo: Parameterise over any terminating way to weaken a term (e.g. to allow
-- using renamings instead of single weakenings)
module Coincidences.Substitutions.Single.Sub where

infixl 100 _[_]s _[_]sv _[_]stm _[_]stys

data Sub : Ctx → Ctx → Set

⟦_⟧s : Sub Δ Γ → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c
_[_]s  : Ty Γ → Sub Δ Γ → Ty Δ
_[_]s≡ : ∀ A (δ : Sub Δ Γ) → ⟦ A [ δ ]s ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧s

data Sub where
  <_> : Tm Γ ⟦ A ⟧T → Sub Γ (Γ , A)
  _↑_ : ∀ (δ : Sub Γ Δ) A → Sub (Γ , A [ δ ]s) (Δ , A)

⟦ < M > ⟧s = sem< ⟦ M ⟧tm >
⟦ δ ↑ A ⟧s (ρ , x) 
  = (⟦ δ ⟧s ↑s ⟦ A ⟧T) (ρ , subst (λ A[] → El (A[] ρ)) ((A [ δ ]s≡)) x) 

_[_]stm  : ∀ {Γ A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧s)

⊥' [ δ ]s = ⊥'
Π' A B [ δ ]s = Π' (A [ δ ]s) (B [ δ ↑ A ]s)
El' A [ δ ]s = El' (A [ δ ]stm) 

⊥' [ δ ]s≡ = refl
Π' A B [ δ ]s≡ 
  = cong (Πsem ⟦ A [ δ ]s ⟧T) B≡ 
  ∙ dcong₂⁻¹ Πsem A≡ ([]-helper ⟦ B ⟧T ⟦ δ ⟧s A≡)
  where A≡ = A [ δ ]s≡
        B≡ = B [ δ ↑ _ ]s≡
El' A [ δ ]s≡ = refl

_[_]stm≡ : ∀ {A} (M : Tm Γ A) (δ : Sub Δ Γ) 
         → ⟦ M [ δ ]stm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧s
_[_]sv  : ∀ {A} → Var Γ A → (δ : Sub Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧s)
_[_]sv≡ : ∀ {A} (x : Var Γ A) (δ : Sub Δ Γ) 
       → ⟦ x [ δ ]sv ⟧tm ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧s

vz   [ < M > ]sv = M
vs x [ < M > ]sv = var x 
vz   [ δ ↑ A ]sv = var (subst (Var _) (cong (_∘ semwk _) (A [ δ ]s≡)) vz)
vs x [ δ ↑ A ]sv = x [ δ ]sv [ wk ]wtm

vz [ < M > ]sv≡ = refl
vs x [ < M > ]sv≡ = refl
vz [ δ ↑ A ]sv≡ = sym ([]v-helper A≡ ∙ lift)
  where
    A≡ = A [ δ ]s≡
    lift = subst-application′ (Var _)
                             {y = vz {A = A [ δ ]s}} 
                             (λ _ → ⟦_⟧v)
                             (cong  (_∘ semwk _) A≡)
vs x [ δ ↑ A ]sv≡ = cong (_∘ semwk _) (x [ δ ]sv≡)

var x [ δ ]stm = x [ δ ]sv
app {B = B} M N [ δ ]stm 
  = subst (λ x → (Tm _ (λ ρ → B (⟦ δ ⟧s ρ , x ρ)))) 
          (N [ δ ]stm≡) (app (M [ δ ]stm) (N [ δ ]stm))
lam {A = A} {B = B} M [ δ ]stm 
  = subst (Tm _) (Πsem≡ refl A≡ (from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧s A≡))) 
          (lam (M [ δ ↑ _ ]stm))
  where
    A≡ = A [ δ ]s≡

var x [ δ ]stm≡ = x [ δ ]sv≡
app {A = A} {B = B} M N [ δ ]stm≡ 
  = sym lift-subst
  ∙ dcong-app (cong appsem (M [ δ ]stm≡)) (N [ δ ]stm≡)
  where lift-subst = subst-application′ (λ x → Tm _ (λ ρ → B (⟦ δ ⟧s ρ , x ρ)))
                                        (λ _ → ⟦_⟧tm) (N [ δ ]stm≡)
lam {A = A} {B = B} M [ δ ]stm≡ 
  = sym lift 
  ∙ cong (subst (SemVal _) coe-eq) 
         (cong (λ M′ ρ → M′ ∘ (ρ ,_)) (M [ δ ↑ _ ]stm≡)) 
  ∙ []tm-helper ⟦ δ ⟧s ⟦ M ⟧tm A≡ B≡
  where A≡ = A [ δ ]s≡
        B≡ = from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧s A≡)
        coe-eq = Πsem≡ refl A≡ B≡
        lift = subst-application′ (Tm _) (λ _ → ⟦_⟧tm) coe-eq

{-# REWRITE _[_]s≡  _[_]sv≡ _[_]stm≡ #-}

_[_]stys : Tys Γ → Sub Δ Γ → Tys Δ
_↑↑s_ : ∀ (δ : Sub Δ Γ) Γ′ → Sub (Δ ++ Γ′ [ δ ]stys) (Γ ++ Γ′)

ε [ δ ]stys = ε
(Γ′ , A) [ δ ]stys = Γ′ [ δ ]stys , A [ δ ↑↑s Γ′ ]s

δ ↑↑s ε = δ     
δ ↑↑s (Γ′ , A) = (δ ↑↑s Γ′) ↑ A
