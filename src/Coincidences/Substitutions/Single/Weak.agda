{-# OPTIONS --prop --show-irrelevant --rewriting --local-confluence-check #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys
open import Coincidences.SemTys
open import Coincidences.Substitutions.Common

-- Single variable weakenings.
-- Prepare for a lot of duplication between weakenings/substitutions. 
-- I don't know how to get rid of this without Agda's termination checker
-- complaining.
module Coincidences.Substitutions.Single.Weak where

infixl 100 _[_]w _[_]wv _[_]wtm _[_]wtys

data Wk  : Ctx → Ctx → Set

⟦_⟧w : Wk Δ Γ  → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c
_[_]w  : Ty Γ → Wk Δ Γ  → Ty Δ
_[_]w≡ : ∀ A (δ : Wk Δ Γ)  → ⟦ A [ δ ]w ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧w

data Wk where
  wk : Wk (Γ , A) Γ
  _↑_ : ∀ (δ : Wk Γ Δ) A → Wk (Γ , A [ δ ]w) (Δ , A)

⟦ wk ⟧w    = semwk _
⟦ δ ↑ A ⟧w (ρ , x) 
  = (⟦ δ ⟧w ↑s ⟦ A ⟧T) (ρ , subst (λ A[] → El (A[] ρ)) ((A [ δ ]w≡)) x) 
_[_]wtm  : ∀ {Γ A} → Tm Γ A → (δ : Wk Δ Γ)  → Tm Δ (A ∘ ⟦ δ ⟧w)

⊥' [ δ ]w = ⊥'
(Π' A B) [ δ ]w = Π' (A [ δ ]w) (B [ δ ↑ A ]w)
El' A [ δ ]w = El' (A [ δ ]wtm) 

⊥' [ δ ]w≡ = refl
Π' A B [ δ ]w≡ 
  = sym (dcong₂ Πsem (sym A≡) ([]-helper ⟦ B ⟧T ⟦ δ ⟧w A≡ ∙ sym B≡))
  where A≡ = A [ δ ]w≡
        B≡ = B [ δ ↑ _ ]w≡
El' A [ δ ]w≡ = refl

_[_]wtm≡ : ∀ {A} (M : Tm Γ A) (δ : Wk Δ Γ) 
         → ⟦ M [ δ ]wtm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧w
_[_]wv : ∀ {A} → Var Γ A → (δ : Wk Δ Γ) → Var Δ (A ∘ ⟦ δ ⟧w)
_[_]wv≡ : ∀ {A} (x : Var Γ A) (δ : Wk Δ Γ) 
        → ⟦ x [ δ ]wv ⟧v ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧w

x    [ wk    ]wv = vs x
vz   [ δ ↑ A ]wv = subst (Var _) (cong (_∘ semwk _) (A [ δ ]w≡)) 
                         (vz {A = A [ δ ]w})
vs x [ δ ↑ A ]wv = vs (x [ δ ]wv)

x [ wk ]wv≡ = refl
vz [ δ ↑ A ]wv≡ 
  = sym lift ∙ []v-helper (A [ δ ]w≡)
  where 
    lift = subst-application′ (Var _)
                             {y = vz {A = A [ δ ]w}} 
                             (λ _ → ⟦_⟧v)
                             (cong  (_∘ semwk _) (A [ δ ]w≡))
vs x [ δ ↑ A ]wv≡ = cong (_∘ proj₁) (x [ δ ]wv≡)

var x [ δ ]wtm = var (x [ δ ]wv)
app {B = B} M N [ δ ]wtm 
  = subst (λ x → (Tm _ (λ ρ → B (⟦ δ ⟧w ρ , x ρ)))) 
          (N [ δ ]wtm≡) (app (M [ δ ]wtm) (N [ δ ]wtm))
lam {A = A} {B = B} M [ δ ]wtm 
  = subst (Tm _) (Πsem≡ refl A≡ (from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧w A≡))) 
          (lam (M [ δ ↑ _ ]wtm))
  where
    A≡ = A [ δ ]w≡

var x [ δ ]wtm≡ = x [ δ ]wv≡
app {A = A} {B = B} M N [ δ ]wtm≡ 
  = sym lift-subst
  ∙ dcong-app (cong appsem (M [ δ ]wtm≡)) (N [ δ ]wtm≡)
  where lift-subst = subst-application′ (λ x → Tm _ (λ ρ → B (⟦ δ ⟧w ρ , x ρ)))
                                        (λ _ → ⟦_⟧tm) (N [ δ ]wtm≡)
lam {A = A} {B = B} M [ δ ]wtm≡ 
  = sym lift 
  ∙ cong (subst (SemVal _) coe-eq) 
         (cong (λ M′ ρ → M′ ∘ (ρ ,_)) (M [ δ ↑ _ ]wtm≡)) 
  ∙ []tm-helper ⟦ δ ⟧w ⟦ M ⟧tm A≡ B≡
  where A≡ = A [ δ ]w≡
        B≡ = from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧w A≡)
        coe-eq = Πsem≡ refl A≡ B≡
        lift = subst-application′ (Tm _) (λ _ → ⟦_⟧tm) coe-eq

{-# REWRITE _[_]w≡ _[_]wv≡ _[_]wtm≡ #-}


_[_]wtys : Tys Γ → Wk Δ Γ → Tys Δ

_↑↑w_ : ∀ (δ : Wk Δ Γ) Γ′ → Wk (Δ ++ Γ′ [ δ ]wtys) (Γ ++ Γ′)

ε [ δ ]wtys = ε
(Γ′ , A) [ δ ]wtys = Γ′ [ δ ]wtys , A [ δ ↑↑w Γ′ ]w

δ ↑↑w ε = δ     
δ ↑↑w (Γ′ , A) = (δ ↑↑w Γ′) ↑ A 
 