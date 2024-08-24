{-# OPTIONS --prop --show-irrelevant --rewriting #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys
open import Coincidences.Substitutions.Common
open import Coincidences.Substitutions.Parallel.Common
open import Coincidences.Substitutions.Parallel.Simul

module Coincidences.Substitutions.Parallel.Comp where



private module Congruences where

  Objs≡ : ∀ {Δ₁ Δ₂ Γ₁ Γ₂} s → Δ₁ ≡ Δ₂ → Γ₁ ≡ Γ₂ → Objs s Δ₁ Γ₁ ≡ Objs s Δ₂ Γ₂
  Objs≡ s = cong₂ (Objs s)
  
  ⟦⟧os≡ : ∀ {Δ₁ Δ₂ Γ₁ Γ₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂) 
         → (δ₁ ≡[ Objs≡ s Δ≡ Γ≡ ]≡ δ₂)
         → ⟦ δ₁ ⟧os ≡[ SemSub≡ ⟦ Δ≡ ⟧c≡ ⟦ Γ≡ ⟧c≡ ]≡ ⟦ δ₂ ⟧os 
  ⟦⟧os≡ refl refl refl = refl

  []tm≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ M₁ M₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
            (A≡ : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂)
            (M≡ : M₁ ≡[ Tm≡ Γ≡ A≡ ]≡ M₂)
            (δ≡ : δ₁ ≡[ Objs≡ s Δ≡ Γ≡ ]≡ δ₂)
        → M₁ [ δ₁ ]tm 
       ≡[ Tm≡ Δ≡ ([]sem≡ ⟦ Δ≡ ⟧c≡ ⟦ Γ≡ ⟧c≡ A≡ (⟦⟧os≡ Γ≡ Δ≡ δ≡)) 
       ]≡ M₂ [ δ₂ ]tm
  []tm≡ refl refl refl refl refl = refl

open Congruences public

max : Sort → Sort → Sort
max V t = t
max (T>V v p) _ = T>V v p

-- max-rightV≡ : ∀ s → max s V ≡ s
-- max-rightV≡ V = refl
-- max-rightV≡ T = refl
-- {-# REWRITE max-rightV≡ #-}

_[_]o : ∀ {A} → Obj s Γ A → (δ : Objs t Δ Γ) → Obj (max s t) Δ (A ∘ ⟦ δ ⟧os) 
_[_]o {s = V} = _[_]v
_[_]o {s = T} = _[_]tm

_[_]o≡ : ∀ {A} (M : Obj s Γ A) (δ : Objs t Δ Γ) 
       → ⟦ M [ δ ]o ⟧o ≡ ⟦ M ⟧o ∘ ⟦ δ ⟧os
_[_]o≡ {s = V} = _[_]v≡
_[_]o≡ {s = T} = _[_]tm≡

{-# REWRITE _[_]o≡ #-}

[]o-obj→tm≡ : ∀ {A} s (M : Obj s Γ A) (δ : Objs t Δ Γ)
            → obj→tm s M [ δ ]tm ≡ obj→tm (max s t) (M [ δ ]o)
[]o-obj→tm≡ V M δ = refl
[]o-obj→tm≡ T M δ = refl

{-# REWRITE []o-obj→tm≡ #-}

↑sorto : ∀ {A} s t → Obj t Γ A → Obj (max s t) Γ A
↑sorto T V = var
↑sorto V _ = id
↑sorto T T = id

↑sorto≡ : ∀ {A} s t (M : Obj t Γ A) → ⟦ ↑sorto s t M ⟧o ≡ ⟦ M ⟧o
↑sorto≡ T V M = refl
↑sorto≡ V _ M = refl
↑sorto≡ T T M = refl

{-# REWRITE ↑sorto≡ #-}

↑sortos : ∀ s → Objs t Δ Γ → Objs (max s t) Δ Γ
↑sortos≡ : ∀ s (δ : Objs t Δ Γ) → ⟦ ↑sortos s δ ⟧os ≡ ⟦ δ ⟧os

↑sortos _ ε = ε
↑sortos {t = t} s (_,_ {A = A} δ M) 
  = ↑sortos s δ , subst (Obj (max s t) _ ∘ (⟦ A ⟧T ∘_)) (sym (↑sortos≡ s δ)) 
                        (↑sorto s t M)

↑sortos≡ s ε = refl
↑sortos≡ {t = t} s (_,_ {A = A} δ M) 
  = dcong₂⁻¹ _,sub_ (↑sortos≡ s δ) (sym rm-subst)
  where δ≡ = ↑sortos≡ s δ
        rm-subst = subst-application′ (Obj (max s t) _ ∘ (⟦ A ⟧T ∘_)) (λ _ → ⟦_⟧o) (sym δ≡)

{-# REWRITE ↑sortos≡ #-}

_∘os_ : Objs s Δ Γ → Objs t θ Δ → Objs (max s t) θ Γ 
_∘os≡_ : ∀ (δ : Objs s Δ Γ) (σ : Objs t θ Δ) → ⟦ δ ∘os σ ⟧os ≡ ⟦ δ ⟧os ∘ ⟦ σ ⟧os

ε ∘os ε = ε
ε ∘os (σ , M) = ε ∘os σ
_∘os_ {s = s} {t = t} (_,_ {A = A} δ M) σ 
  = (δ ∘os σ) 
  , subst (Obj (max s t) _ ∘ (⟦ A ⟧T ∘_)) (sym (δ ∘os≡ σ)) (M [ σ ]o)

ε ∘os≡ ε = refl
_∘os≡_ {s = s} ε (σ , M) = ε {s = s} ∘os≡ σ
_∘os≡_ {s = s} {t = t} (_,_ {A = A} δ M) σ 
  = dcong₂⁻¹ _,sub_ δ≡ (sym rm-subst)
  where δ≡ = δ ∘os≡ σ
        rm-subst = subst-application′ (Obj (max s t) _ ∘ (⟦ A ⟧T ∘_)) 
                                      (λ _ → ⟦_⟧o) (sym δ≡)

{-# REWRITE _∘os≡_ #-}

[]-comp : ∀ A (δ : Objs s Δ Γ) (σ : Objs t θ Δ) → A [ δ ] [ σ ] ≡ A [ δ ∘os σ ]
[]tm-comp : ∀ {A} (M : Tm Γ A) (δ : Objs s Δ Γ) (σ : Objs t θ Δ) 
          → M [ δ ]tm [ σ ]tm ≡ M [ δ ∘os σ ]tm

[]v-comp : ∀ {A} (x : Var Γ A) (δ : Objs s Δ Γ) (σ : Objs t θ Δ) 
         → x [ δ ]v [ σ ]o ≡ x [ δ ∘os σ ]v

↑∘os≡ : ∀ A (δ : Objs s Δ Γ) (σ : Objs t θ Δ) 
      → (δ ↑os A) ∘os (σ ↑os A [ δ ]) 
     ≡[ cong (λ A[] → Objs (max s t) (θ , A[]) (Γ , A)) ([]-comp A δ σ)
     ]≡ (δ ∘os σ) ↑os A


[]-comp ⊥' δ σ = refl
[]-comp {s = s} {t = t} (Π' A B) δ σ 
  = dcong₂⁻¹ Π' A≡ ([]-comp B (δ ↑os _) (σ ↑os _) 
  ∙ dcong (B [_]) (to-coe≡⁻¹ _ (↑∘os≡ A δ σ)) ∙ sym rm-subst)
  where A≡ = []-comp A δ σ
        rm-subst = subst-application′ (λ A[] → Objs (max s t) (_ , A[]) (_ , A)) 
                                      (λ _ → B [_]) (sym A≡)
[]-comp (El' M) δ σ = cong El' ([]tm-comp M δ σ)

[]tm-comp {s = s} {t = t} (var x) δ σ 
  = cong (obj→tm (max s t)) ([]v-comp x δ σ)
[]tm-comp (app M N) δ σ = app≡ refl refl refl M≡ N≡
  where M≡ = []tm-comp M δ σ
        N≡ = []tm-comp N δ σ
-- Nightmare case incoming!!!
[]tm-comp {s = s} {t = t} (lam {A = A} {B = B} M) δ σ 
  = sym rm-subst ∙ coes-cancel2 ∙ sym coes-cancel 
  ∙ cong (subst (Tm _) prf) 
         (to-coe≡ _ (lam≡ refl A[]≡ B[]≡ (_∙P_ {p = refl} M[]≡ ↑[]≡)))
  where M[]≡ = []tm-comp M (δ ↑os _) (σ ↑os _)
        A[]≡ = []-comp A δ σ
        B[]≡ = cong (B ∘_) (cong ((⟦ δ ⟧os ∘ ⟦ σ ⟧os ∘ semwk _) ,sub_)  
            (cong₂ (λ v₁ v₂ → v₁ ∘ ((⟦ σ ⟧os ∘ semwk _) ,sub v₂)) 
                   (vzo≡ {A = A [ δ ]} s) (vzo≡ {A = A [ δ ] [ σ ]} t)
            ∙ sym (vzo≡ {A = A [ δ ∘os σ ]} (max s t))  ))
        ↑[]≡ = []tm≡ refl (refl ,≡ A[]≡) refl (erefl M) (↑∘os≡ A δ σ)
        A≡ = A [ δ ∘os σ ]≡
        M≡ = M [ (δ ∘os σ) ↑os _ ]tm≡
        lamM≡ = lamsem≡ refl refl refl M≡
        prf = dcong₂⁻¹ Πsem A≡ (cong (B ∘_) (((δ ∘os σ) ↑os≡ A) 
            ∙ ↑[]-helper _ A≡ ∙ cong (_ ,sub_) (sym (semvz-helper A≡)))
            ∙ []-helper B ⟦ δ ∘os σ ⟧os A≡)
        Aδ≡ = A [ δ ]≡
        prfδ = dcong₂⁻¹ Πsem Aδ≡ (cong (B ∘_) ((δ ↑os≡ A) 
            ∙ ↑[]-helper _ Aδ≡ ∙ cong (_ ,sub_) (sym (semvz-helper Aδ≡)))
            ∙ []-helper B ⟦ δ ⟧os Aδ≡)
        coes-cancel = coe-coe _ (cong (Tm _) prf) 
                                (cong (Tm _) (Πsem≡ refl (⟦⟧T≡ refl A[]≡) B[]≡))
        coes-cancel2 = coe-coe (lam (M [ wkos (A [ δ ]) δ , vzo s ]tm 
                                       [ wkos (A [ δ ] [ σ ]) σ , vzo t ]tm)) 
                               (cong (Tm _ ∘ (_∘ ⟦ σ ⟧os)) prfδ) _
        rm-subst = subst-application′ (Tm _) (λ _ → _[ σ ]tm) prfδ

-- (wkos (A [ δ ]) δ ∘os (wkos (A [ δ ] [ σ ]) σ , vz)) , vz
-- = (wkos (A [ δ ]) δ ∘os (σ ↑os A [ δ ])) , vz

-- wkos (A [ δ ∘os σ ]) (δ ∘os σ) , vz
-- = (δ ∘os σ) ↑os A

-- Focus
--   wkos (A [ δ ]) δ ∘os (σ ↑os A [ δ ])
-- ≡ wkos (A [ δ ∘os σ ]) (δ ∘os σ)


[]v-comp vz (δ , M) σ = refl
[]v-comp (vs x) (δ , M) σ = []v-comp x δ σ

wk∘os≡ : ∀ A (δ : Objs s Δ Γ) (σ : Objs t θ Δ) 
       → wkos (A [ δ ∘os σ ]) (δ ∘os σ) 
      ≡[ cong (λ δσ → Objs (max s t) (θ , δσ) Γ) (sym ([]-comp A δ σ)) 
      ]≡ wkos (A [ δ ]) δ ∘os (σ ↑os A [ δ ])
wk∘os≡ A ε ε = {!!}
wk∘os≡ A ε (σ , M) = _∙P_ (wk∘os≡ A ε σ) {!!}
wk∘os≡ A (δ , M) σ = {!wk∘os≡ _ δ σ   !}

↑∘os≡ {s = V} {t = V} A ε ε = {!   !}
↑∘os≡ {s = V} {t = V} A ε (σ , M) = {!↑∘os≡ A ε σ   !}
↑∘os≡ {s = V} {t = V} A (δ , M) σ = {!↑∘os≡ _ δ σ   !}
-- ↑∘os≡ {s = V} {t = V} (Π' A B) δ σ = {!   !}
-- ↑∘os≡ {s = V} {t = V} (El' M) δ σ = {!   !}
 
-- ↑∘os≡ {s = V} {t = V} A ε σ = from-coe≡⁻¹ _ {!   !} 
-- ↑∘os≡ {s = V} {t = V} A (δ , M) σ = {!   !} 