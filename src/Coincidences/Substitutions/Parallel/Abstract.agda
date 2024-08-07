{-# OPTIONS --prop --show-irrelevant --rewriting --local-confluence-check #-}
open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys
open import Coincidences.Substitutions.Common
open import Coincidences.Substitutions.Parallel.Common

module Coincidences.Substitutions.Parallel.Abstract 
  (O : ∀ Γ → SemTy ⟦ Γ ⟧c → Set) (⟦_⟧o : ∀ {Γ A} → O Γ A → SemVal ⟦ Γ ⟧c A) 
  (vzo  : ∀ {Γ A} → O (Γ , A) (⟦ A ⟧T ∘ semwk _)) 
  (vzo≡ : ∀ {Γ A} → ⟦ vzo {Γ} {A} ⟧o ≡ semvz)
  (wko  : ∀ {Γ B} A → O Γ B → O (Γ , A) (B ∘ semwk _))
  (wko≡ : ∀ {Γ B} A (M : O Γ B) →  ⟦ wko A M ⟧o ≡ ⟦ M ⟧o ∘ semwk _)
  (tm-embed : ∀ {Γ A} → O Γ A → Tm Γ A)
  (tm-embed≡ : ∀ {Γ A} (M : O Γ A) → ⟦ tm-embed M ⟧tm ≡ ⟦ M ⟧o)
  where

data Objects : Ctx → Ctx → Set
⟦_⟧os : Objects Δ Γ → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c

data Objects where
  ε   : Objects Δ ε
  _,_ : ∀ ρ → O Δ (⟦ A ⟧T ∘ ⟦ ρ ⟧os) → Objects Δ (Γ , A)

⟦ ε ⟧os = semwk* _
⟦ ρ , M ⟧os = ⟦ ρ ⟧os ,sub ⟦ M ⟧o

wkos : ∀ A → Objects Δ Γ → Objects (Δ , A) Γ
wkos≡ : ∀ A (δ : Objects Δ Γ) → ⟦ wkos A δ ⟧os ≡ ⟦ δ ⟧os ∘ semwk _

wkos A ε = ε
wkos A (_,_ {A = B} δ M) 
  = wkos A δ , subst (O _ ∘ (⟦ B ⟧T ∘_)) (sym (wkos≡ A δ)) (wko A M)

wkos≡ A ε = refl
wkos≡ A (_,_ {A = B} δ M) 
  =  dcong₂⁻¹ _,sub_ δ≡ (sym rm-subst 
  ∙ cong (subst (SemVal _ ∘ (⟦ B ⟧T ∘_)) (sym δ≡)) wkM≡)
  where δ≡ = wkos≡ A δ
        wkM≡ = wko≡ A M
        rm-subst = subst-application′ (O (_ , A) ∘ (⟦ B ⟧T ∘_)) (λ _ → ⟦_⟧o) 
                                      (sym δ≡)

_[_]   : Ty Γ → Objects Δ Γ → Ty Δ
_[_]v  : ∀ {A} → Var Γ A → ∀ δ → O Δ (A ∘ ⟦ δ ⟧os)
_[_]tm : ∀ {A} → Tm Γ A → ∀ δ → Tm Δ (A ∘ ⟦ δ ⟧os)

_[_]≡ : ∀ (A : Ty Γ) (δ : Objects Δ Γ) → ⟦ A [ δ ] ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧os
_[_]tm≡ : ∀ {A} (M : Tm Γ A) → (δ : Objects Δ Γ) 
        → ⟦ M [ δ ]tm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧os
_[_]v≡ : ∀ {A} (x : Var Γ A) → (δ : Objects Δ Γ) 
       → ⟦ x [ δ ]v ⟧o ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧os

_↑os_ : ∀ (δ : Objects Δ Γ) A → Objects (Δ , A [ δ ]) (Γ , A)
δ ↑os A = wkos (A [ δ ]) δ , subst (O _) (cong (_∘ semwk _) A≡
        ∙ cong (⟦ A ⟧T ∘_) (sym (wkos≡ (A [ δ ]) δ))) vzo
  where A≡ = A [ δ ]≡

_↑os≡_ : ∀ (δ : Objects Δ Γ) A
     → ⟦ δ ↑os A ⟧os 
    ≡[ cong₂ SemSub (cong (_ ,s_ ) (A [ δ ]≡)) refl 
    ]≡ ⟦ δ ⟧os ↑s ⟦ A ⟧T
δ ↑os≡ A
  = from-coe≡⁻¹ _ (dcong₂⁻¹ _,sub_ wkδ≡ (sym rm-subst 
  ∙ cong (subst (SemVal ⟦ _ , (A [ δ ]) ⟧c) prf) vzo≡ ∙ coes-cancel)
  ∙ sym (↑[]-helper ⟦ δ ⟧os A≡))
  where
    A≡ = A [ δ ]≡
    wkδ≡ = wkos≡ (A [ δ ]) δ
    prf = (cong (λ section x → section (semwk ⟦ A [ δ ] ⟧T x))
           A≡
           ∙
           cong (λ section x → ⟦ A ⟧T (section x)) (sym (wkos≡ (A [ δ ]) δ)))
    rm-subst = subst-application′ (O (_ , (A [ δ ]))) (λ _ → ⟦_⟧o) prf
    coes-cancel = sym (coe-coe semvz _ (cong (SemVal _ ∘ (_∘ semwk ⟦ A [ δ ] ⟧T)) A≡))

⊥' [ δ ] = ⊥'
Π' A B [ δ ] = Π' (A [ δ ]) (B [ δ ↑os A ])
El' M [ δ ] = El' (M [ δ ]tm)

⊥' [ δ ]≡ = refl
Π' A B [ δ ]≡ 
  = dcong₂⁻¹ Πsem A≡ (B≡ ∙ cong (⟦ B ⟧T ∘_) (to-coe≡⁻¹ _ (δ ↑os≡ A) 
  ∙ sym (↑-helper ⟦ A ⟧T ⟦ δ ⟧os ⟦ A [ δ ] ⟧T A≡))
  ∙ []-helper ⟦ B ⟧T ⟦ δ ⟧os A≡)
  where A≡ = A [ δ ]≡
        B≡ = B [ δ ↑os A ]≡
El' M [ δ ]≡ = refl

vz [ δ , M ]v = M
vs x [ δ , M ]v = x [ δ ]v

vz [ δ , M ]v≡ = refl
vs x [ δ , M ]v≡ = x [ δ ]v≡

var x [ δ ]tm = tm-embed (x [ δ ]v)
app {B = B} M N [ δ ]tm 
  = subst (λ N[] → Tm _ (B ∘ (⟦ δ ⟧os ,sub N[]))) (N [ δ ]tm≡) 
          (app (M [ δ ]tm) (N [ δ ]tm))
lam {A = A} {B = B} M [ δ ]tm 
  = subst (Tm _) (dcong₂⁻¹ Πsem A≡ (cong (B ∘_) (to-coe≡⁻¹ _ (δ ↑os≡ A) 
  ∙ ↑[]-helper _ A≡ ∙ cong (_ ,sub_) (sym (semvz-helper A≡)))
  ∙ []-helper B ⟦ δ ⟧os A≡)) 
    (lam (M [ δ ↑os _ ]tm))
  where A≡ = A [ δ ]≡

var x [ δ ]tm≡ = tm-embed≡ _ ∙ x [ δ ]v≡
app {B = B} M N [ δ ]tm≡ = sym rm-subst ∙ to-coe≡ _ MN≡
  where M≡ = M [ δ ]tm≡
        N≡ = N [ δ ]tm≡ 
        MN≡ = appsem≡ refl refl refl M≡ N≡
        rm-subst = subst-application′ (λ N[] → Tm _ (B ∘ (⟦ δ ⟧os ,sub N[]))) 
                                      (λ _ → ⟦_⟧tm) N≡
lam {A = A} {B = B} M [ δ ]tm≡ 
  = sym rm-subst2 ∙ cong (subst (SemVal _) prf) (to-coe≡ refl lamM≡)
  ∙ cong (subst (SemVal _) prf ∘ lamsem) (dcong⁻¹ (⟦ M ⟧tm ∘_) ↑≡)
  ∙ []lam≡-helper ⟦ δ ⟧os ⟦ M ⟧tm A≡ (sym ↑≡) prf
  where A≡ = A [ δ ]≡
        M≡ = M [ δ ↑os _ ]tm≡
        lamM≡ = lamsem≡ refl refl refl M≡
        prf = dcong₂⁻¹ Πsem A≡ (cong (B ∘_) (to-coe≡⁻¹ _ (δ ↑os≡ A) 
            ∙ ↑[]-helper _ A≡ ∙ cong (_ ,sub_) (sym (semvz-helper A≡)))
            ∙ []-helper B ⟦ δ ⟧os A≡)
        rm-subst2 = subst-application′ (Tm _) (λ _ → ⟦_⟧tm) prf
        ↑≡ = to-coe≡⁻¹ _ (δ ↑os≡ A)
 