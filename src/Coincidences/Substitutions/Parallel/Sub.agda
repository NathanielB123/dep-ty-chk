{-# OPTIONS --prop --show-irrelevant --rewriting #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys
open import Coincidences.Substitutions.Common
open import Coincidences.Substitutions.Parallel.Common

-- Parallel substitutions

-- We parameterise Sub over a way to implement weakenings (either renamings or
-- single-variable weakenings work fine for our purposes)
module Coincidences.Substitutions.Parallel.Sub 
       (weaken-tm : ∀ {Γ B} A → Tm Γ B → Tm (Γ , A) (B ∘ semwk ⟦ A ⟧T))
       (weaken-tm≡ : ∀ {Γ B} A (M : Tm Γ B) 
                   → ⟦ weaken-tm A M ⟧tm ≡ ⟦ M ⟧tm ∘ semwk ⟦ A ⟧T)
       where

infixl 100 _[_]

-- Cursed hack to make 'weaken-tm≡' definitional
postulate wktm : ∀ {B} A → Tm Γ B → Tm (Γ , A) (B ∘ semwk ⟦ A ⟧T)
postulate wktm≡ : ∀ {B} A (M : Tm Γ B) → ⟦ wktm A M ⟧tm ≡ ⟦ M ⟧tm ∘ semwk ⟦ A ⟧T
postulate justify-wktm : (λ {Γ} {B} → wktm {Γ = Γ} {B = B}) ≡ weaken-tm

{-# REWRITE wktm≡ #-}

semwktms : ∀ {Γ Δ} A → SemSub Δ Γ → SemSub (Δ ,s A) Γ
semwktms _ δ (ρ , _) = δ ρ

wktms : ∀ A → Tms Δ Γ → Tms (Δ , A) Γ
wktms≡ : ∀ A (δ : Tms Δ Γ) → ⟦ wktms A δ ⟧tms ≡ semwktms ⟦ A ⟧T ⟦ δ ⟧tms

wktms B ε = ε
wktms B (_,_ {A = A} δ M) 
  = wktms B δ , subst (Tm _ ∘ (⟦ A ⟧T ∘_)) (sym (wktms≡ B δ)) (wktm B M)

wktms≡ B ε = refl
wktms≡ B (_,_ {A = A} δ x) = sym (dcong₂ _,sub_ (sym δ≡) rm-subst)
  where δ≡ = wktms≡ B δ
        rm-subst = subst-application′ (Tm (_ , B) ∘ (⟦ A ⟧T ∘_)) (λ _ → ⟦_⟧tm) 
                                      (sym δ≡)
{-# REWRITE wktms≡ #-}

_[_] : Ty Γ → Tms Δ Γ → Ty Δ
_[_]≡ : ∀ A (δ : Tms Δ Γ) → ⟦ A [ δ ] ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧tms

_[_]tm : ∀ {A} → Tm Γ A → ∀ δ → Tm Δ (A ∘ ⟦ δ ⟧tms)
_[_]v : ∀ {A} → Var Γ A → ∀ δ → Tm Δ (A ∘ ⟦ δ ⟧tms)

_↑ts_ : ∀ (δ : Tms Δ Γ) A → Tms (Δ , A [ δ ]) (Γ , A)
δ ↑ts A 
  = wktms (A [ δ ]) δ 
  , var (subst {y = ⟦ A ⟧T ∘ ⟦ δ ⟧tms} (Var (_ , A [ δ ]) ∘ (_∘ semwk _)) 
               (A [ δ ]≡) vz)
{-# INLINE _↑ts_ #-}

↑ts≡ : ∀ (δ : Tms Δ Γ) A
     → ⟦ δ ↑ts A ⟧tms 
    ≡[ cong₂ SemSub (cong (_ ,s_ ) (A [ δ ]≡)) refl 
    ]≡ ⟦ δ ⟧tms ↑s ⟦ A ⟧T

⊥' [ δ ] = ⊥'
Π' A B [ δ ] = Π' (A [ δ ]) (B [ δ ↑ts A ])
El' M [ δ ] = El' (M [ δ ]tm)

⊥' [ δ ]≡ = refl
Π' A B [ δ ]≡ 
  = sym (dcong₂ Πsem (sym A≡) ([]-helper ⟦ B ⟧T ⟦ δ ⟧tms A≡ 
  ∙ cong (⟦ B ⟧T ∘_) (↑-helper ⟦ A ⟧T ⟦ δ ⟧tms ⟦ A [ δ ] ⟧T A≡ 
  ∙ to-coe≡ _ (symm (↑ts≡ δ A))) ∙ sym B≡))
  where A≡ = A [ δ ]≡
        B≡ = B [ δ ↑ts A ]≡
El' M [ δ ]≡ = refl

↑ts≡ δ A = from-coe≡⁻¹ _ (↑[]-helper ⟦ δ ⟧tms A≡ 
         ∙ cong ((⟦ δ ⟧tms ∘ semwk _) ,sub_) rm-subst)
  where
    A≡ = A [ δ ]≡
    rm-subst = subst-application′ (λ A′ → Var (_ , (A [ δ ])) 
                                  (A′ ∘ (semwk ⟦ A [ δ ] ⟧T))) (λ _ → ⟦_⟧v) A≡

_[_]tm≡ : ∀ {A} (M : Tm Γ A) → (δ : Tms Δ Γ) 
        → ⟦ M [ δ ]tm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧tms
_[_]v≡ : ∀ {A} (M : Var Γ A) → (δ : Tms Δ Γ) 
       → ⟦ M [ δ ]v ⟧tm ≡ ⟦ M ⟧v ∘ ⟦ δ ⟧tms

var x [ δ ]tm = x [ δ ]v
app {B = B} M N [ δ ]tm 
  = subst (λ N[] → Tm _ (B ∘ (⟦ δ ⟧tms ,sub N[]))) (N [ δ ]tm≡) 
          (app (M [ δ ]tm) (N [ δ ]tm))
lam {A = A} {B = B} M [ δ ]tm 
  = subst (Tm _) (Πsem≡ refl A≡ (from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧tms A≡ 
  ∙ cong ((B ∘_) ∘ ((⟦ δ ⟧tms ∘ semwk _) ,sub_)) 
         ([]lam-helper ⟦ δ ⟧tms ⟦ A ⟧T A≡ ∙ rm-subst)))) 
         (lam (M [ δ ↑ts _ ]tm))
  where A≡ = A [ δ ]≡
        rm-subst = subst-application′ (λ A′ → Var (_ , A [ δ ]) (A′ ∘ semwk _))
                                      (λ _ → ⟦_⟧v) A≡

var x [ δ ]tm≡ = x [ δ ]v≡
app {A = A} {B = B} M N [ δ ]tm≡ 
  = sym rm-subst ∙ to-coe≡ _ (appsem≡ refl refl refl M≡ N≡)
  where N≡ = N [ δ ]tm≡
        M≡ = M [ δ ]tm≡
        foo = appsem≡ refl refl refl M≡ N≡
        rm-subst = subst-application′ (λ N[] → Tm _ (B ∘ (⟦ δ ⟧tms ,sub N[]))) 
                                      (λ _ → ⟦_⟧tm) N≡
lam {A = A} {B = B} M [ δ ]tm≡ 
  = sym rm-subst2 
  ∙ cong (subst (SemVal _) prf) (to-coe≡ refl (lamsem≡ refl refl refl M≡) 
  ∙ cong lamsem (sym (dcong (⟦ M ⟧tm ∘_) ↑≡)))
  ∙ []lam≡-helper ⟦ δ ⟧tms ⟦ M ⟧tm A≡ ↑≡ prf
  where
    A≡ = A [ δ ]≡
    M≡ = M [ δ ↑ts _ ]tm≡
    rm-subst = subst-application′ (λ A′ → Var (_ , A [ δ ]) (A′ ∘ semwk _))
                                  (λ _ → ⟦_⟧v) A≡
    prf = (Πsem≡ refl A≡ (from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧tms A≡ 
        ∙ cong ((B ∘_) ∘ ((⟦ δ ⟧tms ∘ semwk _) ,sub_)) 
         ([]lam-helper ⟦ δ ⟧tms ⟦ A ⟧T A≡ ∙ rm-subst)))) 
    rm-subst2 = subst-application′ (Tm _) (λ _ → ⟦_⟧tm) prf
    ↑≡ = to-coe≡⁻¹ _ (↑ts≡ δ A)

vz [ δ , M ]v = M
vs x [ δ , M ]v = x [ δ ]v

vz [ δ , M ]v≡ = refl
vs x [ δ , M ]v≡ = x [ δ ]v≡

id-tms : Tms Γ Γ
id-tms = ren-to-sub (id-ren _)

<_> : Tm Γ ⟦ A ⟧T → Tms Γ (Γ , A)
< M > = id-tms , M

{-# REWRITE _[_]≡ _[_]tm≡ _[_]v≡ #-}
-- {-# REWRITE ↑ts≡ #-}

{-# REWRITE justify-wktm #-}  