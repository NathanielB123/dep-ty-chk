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

max-ss≡ : ∀ s → max s s ≡ s
max-ss≡ V = refl
max-ss≡ T = refl
{-# REWRITE max-ss≡ #-}


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

wk-vs≡ : ∀ {A} (x : Var Γ A) (δ : Vars Δ Γ) → x [ wkos B δ ]v ≡ vs (x [ δ ]v)
wk-vs≡ vz (δ , y) = refl
wk-vs≡ (vs x) (δ , y) = wk-vs≡ x δ

{-# REWRITE wk-vs≡ #-}

[id]v≡ : ∀ {A} (x : Var Γ A) → x [ id-os Γ ]v ≡ x
[id]v≡ vz = refl
[id]v≡ (vs x) = cong vs ([id]v≡ x)

{-# REWRITE [id]v≡ #-}

wko-wkos-v≡ : ∀ {A} (x : Var Γ A) (δ : Objs s Δ Γ) 
            → wko s B (x [ δ ]v) ≡ x [ wkos B δ ]v
wko-wkos-v≡ vz (δ , M) = refl
wko-wkos-v≡ (vs x) (δ , M) = wko-wkos-v≡ x δ

wko-wkos-tm≡ : ∀ {A} (M : Tm Γ A) (δ : Objs s Δ Γ) 
             → wko mkT B (M [ δ ]tm) ≡ M [ wkos B δ ]tm
wko-wkos-tm≡ (var x) δ = {!wko-wkos-v≡ x δ !}
-- wko-wkos-tm≡ {s = V} (var x) δ = {!cong var (wko-wkos-v≡ x δ)!}
-- wko-wkos-tm≡ {s = T} (var x) δ = {!wko-wkos-v≡ x δ!}
wko-wkos-tm≡ (app M N) δ = {!   !}
wko-wkos-tm≡ (lam M) δ = {!   !}

-- {-# REWRITE wko-wkos-v≡ #-}
-- wko-wkos≡ : ∀ {A} (M : Obj s Γ A) (δ : Objs t Δ Γ) 
--           → wko (max s t) B (M [ δ ]o) ≡ M [ wkos B δ ]o
-- wko-wkos≡ {s = V} M δ = {! M !}


_∘os_ : Objs s Δ Γ → Objs t θ Δ → Objs (max s t) θ Γ 
_∘os≡_ : ∀ (δ : Objs s Δ Γ) (σ : Objs t θ Δ) → ⟦ δ ∘os σ ⟧os ≡ ⟦ δ ⟧os ∘ ⟦ σ ⟧os

ε ∘os ε = ε
_∘os_ {s = s} ε (σ , M) = _∘os_ {s = s} ε σ
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

wk∘-os : ∀ A (δ : Objs s Δ Γ) (σ : Objs t θ Δ)
       → wkos A (δ ∘os σ) ≡ δ ∘os wkos A σ
wk∘-os A ε ε = refl
wk∘-os A ε (σ , M) = wk∘-os A ε σ
wk∘-os A (δ , M) σ = dcong₂ _,_ (wk∘-os A δ σ) {!   !}


∘id-os : ∀ (δ : Objs s Δ Γ) → δ ∘os id-os {s = s} Δ ≡ δ 
∘id-os (ε {Γ = ε}) = refl
∘id-os (ε {Γ = Δ , A}) = {! !} ∙ cong (wkos A) (∘id-os ε)
∘id-os (δ , M) = {!   !}


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

[]v-comp vz (δ , M) σ = refl
[]v-comp (vs x) (δ , M) σ = []v-comp x δ σ

-- wkos (A [ δ ∘os σ ]) (δ ∘os σ)
-- ≡ (wkos (A [ δ ]) δ ∘os (wkos (A [ δ ] [ σ ]) σ , vzo t))

-- ≡ (wkos (A [ δ ]) δ ∘os (wkos (A [ δ ∘os σ ]) σ , vzo t))

-- (wkos (A [ (δ ∘os σ) , (M [ σ ]o) ]) (δ ∘os σ) ,
      --  wko (max s t) (A [ (δ ∘os σ) , (M [ σ ]o) ]) (M [ σ ]o))

      
-- ((wkos (A [ δ , M ]) δ ∘os (wkos (A [ δ , M ] [ σ ]) σ , vzo t)) ,
--  (wko s (A [ δ , M ]) M [ wkos (A [ δ , M ] [ σ ]) σ , vzo t ]o))
-- ≡ ((wkos (A [ δ , M ]) δ ∘os (wkos (A [ δ ∘os σ , M [ σ ] ]) σ , vzo t)) ,
--  (wko s (A [ δ , M ]) M [ wkos (A [ δ ∘os σ , M [ σ ] ]) σ , vzo t ]o))


wk∘os≡ : ∀ A (δ : Objs s Δ Γ) (σ : Objs t θ Δ) 
       → wkos (A [ δ ∘os σ ]) (δ ∘os σ) 
      ≡[ cong (λ δσ → Objs (max s t) (θ , δσ) Γ) (sym ([]-comp A δ σ)) 
      ]≡ wkos (A [ δ ]) δ ∘os (σ ↑os A [ δ ])
wk∘os≡ A ε ε = {! !} -- ε≡ and done here
wk∘os≡ {s = s} {t = t} A ε (σ , M) 
  = wk∘os≡ A ε σ
 ∙P (from-coe≡ (cong (λ A[] → Objs (max s t) (_ , A[]) ε) A≡) 
    (dcong (λ A[] → _∘os_ {s = s} ε (wkos A[] σ)) A≡))
  where A≡ = []-comp A ε σ ∙ sym ([]-comp A ε (σ , M))
wk∘os≡ A (_,_ {A = B} δ M) σ = {!rec !}
  -- where rec = wk∘os≡ (A [ δ , M ]) σ (id-os _)

↑∘os≡ {s = V} {t = V} A ε ε = {!   !}
↑∘os≡ {s = V} {t = V} A ε (σ , M) = {!↑∘os≡ A ε σ   !}
↑∘os≡ {s = V} {t = V} A (δ , M) σ = {!↑∘os≡ _ δ σ   !}
-- ↑∘os≡ {s = V} {t = V} (Π' A B) δ σ = {!   !}
-- ↑∘os≡ {s = V} {t = V} (El' M) δ σ = {!   !}
  
-- ↑∘os≡ {s = V} {t = V} A ε σ = from-coe≡⁻¹ _ {!   !} 
-- ↑∘os≡ {s = V} {t = V} A (δ , M) σ = {!   !}  