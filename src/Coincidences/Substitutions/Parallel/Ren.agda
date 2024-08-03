{-# OPTIONS --prop --show-irrelevant --rewriting --local-confluence-check #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys
open import Coincidences.Substitutions.Common
open import Coincidences.Substitutions.Parallel.Common

module Coincidences.Substitutions.Parallel.Ren where

wkvars : ∀ A → Vars Δ Γ → Vars (Δ , A) Γ
wkvars≡ : ∀ A (δ : Vars Δ Γ) → ⟦ wkvars A δ ⟧vs ≡ ⟦ δ ⟧vs ∘ semwk ⟦ A ⟧T

wkvars B ε = ε
wkvars B (_,_ {A = A} δ x) 
  = wkvars B δ , subst (Var _ ∘ (⟦ A ⟧T ∘_)) (sym (wkvars≡ B δ)) (vs x)

wkvars≡ B ε = refl
wkvars≡ B (_,_ {A = A} δ x) = sym (dcong₂ _,sub_ (sym δ≡) rm-subst)
  where δ≡ = wkvars≡ B δ
        rm-subst = subst-application′ (Var (_ , B) ∘ (⟦ A ⟧T ∘_)) (λ _ → ⟦_⟧v) 
                                      (sym δ≡)
{-# REWRITE wkvars≡ #-}

_[_]r : Ty Γ → Vars Δ Γ → Ty Δ
_[_]r≡ : ∀ A (δ : Vars Δ Γ) → ⟦ A [ δ ]r ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧vs

_[_]rtm : ∀ {A} → Tm Γ A → ∀ δ → Tm Δ (A ∘ ⟦ δ ⟧vs)
_[_]rv : ∀ {A} → Var Γ A → ∀ δ → Var Δ (A ∘ ⟦ δ ⟧vs)

_↑vs_ : ∀ (δ : Vars Δ Γ) A → Vars (Δ , A [ δ ]r) (Γ , A)
δ ↑vs A 
  = wkvars (A [ δ ]r) δ 
  , subst (Var (_ , A [ δ ]r) ∘ (_∘ semwk _)) (A [ δ ]r≡) vz

↑vs≡ : ∀ (δ : Vars Δ Γ) A
     → ⟦ δ ↑vs A ⟧vs 
    ≡[ cong₂ SemSub (cong (_ ,s_ ) (A [ δ ]r≡)) refl 
    ]≡ ⟦ δ ⟧vs ↑s ⟦ A ⟧T

⊥' [ δ ]r = ⊥'
Π' A B [ δ ]r = Π' (A [ δ ]r) (B [ δ ↑vs A ]r)
El' M [ δ ]r = El' (M [ δ ]rtm)

⊥' [ δ ]r≡ = refl
Π' A B [ δ ]r≡ 
  = sym (dcong₂ Πsem (sym A≡) ([]-helper ⟦ B ⟧T ⟦ δ ⟧vs A≡ 
  ∙ cong (⟦ B ⟧T ∘_) (↑-helper ⟦ A ⟧T ⟦ δ ⟧vs ⟦ A [ δ ]r ⟧T A≡ 
  ∙ to-coe≡ _ (symm (↑vs≡ δ A))) ∙ sym B≡))
  where A≡ = A [ δ ]r≡
        B≡ = B [ δ ↑vs A ]r≡
El' M [ δ ]r≡ = refl

↑vs≡ δ A = from-coe≡⁻¹ _ (↑[]-helper ⟦ δ ⟧vs A≡ 
         ∙ cong ((⟦ δ ⟧vs ∘ semwk _) ,sub_) rm-subst)
  where
    A≡ = A [ δ ]r≡
    rm-subst = subst-application′ (λ A′ → Var (_ , (A [ δ ]r)) 
                                  (A′ ∘ (semwk ⟦ A [ δ ]r ⟧T))) (λ _ → ⟦_⟧v) A≡

_[_]rtm≡ : ∀ {A} (M : Tm Γ A) → (δ : Vars Δ Γ) 
        → ⟦ M [ δ ]rtm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧vs
_[_]rv≡ : ∀ {A} (x : Var Γ A) → (δ : Vars Δ Γ) 
       → ⟦ x [ δ ]rv ⟧v ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧vs

var x [ δ ]rtm = var (x [ δ ]rv)
app {B = B} M N [ δ ]rtm 
  = subst (λ N[] → Tm _ (B ∘ (⟦ δ ⟧vs ,sub N[]))) (N [ δ ]rtm≡) 
          (app (M [ δ ]rtm) (N [ δ ]rtm))
lam {A = A} {B = B} M [ δ ]rtm 
  = subst (Tm _) (Πsem≡ refl A≡ (from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧vs A≡ 
  ∙ cong ((B ∘_) ∘ ((⟦ δ ⟧vs ∘ semwk _) ,sub_)) 
         ([]lam-helper ⟦ δ ⟧vs ⟦ A ⟧T A≡ ∙ rm-subst)))) 
         (lam (M [ δ ↑vs _ ]rtm))
  where A≡ = A [ δ ]r≡
        rm-subst = subst-application′ (λ A′ → Var (_ , A [ δ ]r) (A′ ∘ semwk _))
                                      (λ _ → ⟦_⟧v) A≡

var x [ δ ]rtm≡ = x [ δ ]rv≡
app {A = A} {B = B} M N [ δ ]rtm≡ 
  = sym rm-subst ∙ to-coe≡ _ (appsem≡ refl refl refl M≡ N≡)
  where N≡ = N [ δ ]rtm≡
        M≡ = M [ δ ]rtm≡
        foo = appsem≡ refl refl refl M≡ N≡
        rm-subst = subst-application′ (λ N[] → Tm _ (B ∘ (⟦ δ ⟧vs ,sub N[]))) 
                                      (λ _ → ⟦_⟧tm) N≡
lam {A = A} {B = B} M [ δ ]rtm≡ 
  = sym rm-subst2 
  ∙ cong (subst (SemVal _) prf) (to-coe≡ refl (lamsem≡ refl refl refl M≡) 
  ∙ cong lamsem (sym (dcong (⟦ M ⟧tm ∘_) ↑≡)))
  ∙ []lam≡-helper ⟦ δ ⟧vs ⟦ M ⟧tm A≡ ↑≡ prf
  where
    A≡ = A [ δ ]r≡
    M≡ = M [ δ ↑vs _ ]rtm≡
    rm-subst = subst-application′ (λ A′ → Var (_ , A [ δ ]r) (A′ ∘ semwk _))
                                  (λ _ → ⟦_⟧v) A≡
    prf = (Πsem≡ refl A≡ (from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧vs A≡ 
        ∙ cong ((B ∘_) ∘ ((⟦ δ ⟧vs ∘ semwk _) ,sub_)) 
         ([]lam-helper ⟦ δ ⟧vs ⟦ A ⟧T A≡ ∙ rm-subst)))) 
    rm-subst2 = subst-application′ (Tm _) (λ _ → ⟦_⟧tm) prf
    ↑≡ = to-coe≡⁻¹ _ (↑vs≡ δ A)

vz [ δ , M ]rv = M
vs x [ δ , M ]rv = x [ δ ]rv

vz [ δ , M ]rv≡ = refl
vs x [ δ , M ]rv≡ = x [ δ ]rv≡


{-# REWRITE _[_]r≡ _[_]rtm≡ _[_]rv≡ #-}

wk-vars : Vars (Γ , A) Γ
wk-vars = wkvars _ (id-ren _)
