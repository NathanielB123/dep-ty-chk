{-# OPTIONS --prop --show-irrelevant --rewriting #-}
-- Agda really doesn't like most of the rewrite rules here - oh well!
--local-confluence-check

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys
open import Coincidences.Substitutions.Common
open import Coincidences.Substitutions.Parallel.Common

open import Data.Nat using (ℕ; suc; zero)

module Coincidences.Substitutions.Parallel.Simul where

-- Thanks to Thorsten Altenkirch for coming up with this trick!
-- https://agda.zulipchat.com/#narrow/stream/238741-general/topic/termination.20with.20order.20on.20the.20constructors/near/460052620
data Sort : Set where
  V   : Sort
  T>V : (v : Sort) → v ≡ V → Sort

pattern T = T>V _ _

Obj : Sort → ∀ Γ → SemTy ⟦ Γ ⟧c → Set
Obj V = Var
Obj T = Tm

variable
  s : Sort

⟦_⟧o : ∀ {A} → Obj s Γ A → SemVal ⟦ Γ ⟧c A
⟦_⟧o {s = V} = ⟦_⟧v
⟦_⟧o {s = T} = ⟦_⟧tm

data Objs (s : Sort) : Ctx → Ctx → Set

⟦_⟧os : Objs s Δ Γ → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c

data Objs s where
  ε   : Objs s Γ ε
  _,_ : ∀ (δ : Objs s Δ Γ) → Obj s Δ (⟦ A ⟧T ∘ ⟦ δ ⟧os) → Objs s Δ (Γ , A)

⟦ ε ⟧os = semwk* (build _)
⟦ δ , M ⟧os = ⟦ δ ⟧os ,sub ⟦ M ⟧o

Tms = Objs (T>V V refl)
Vars = Objs V

obj→tm : ∀ {A} s → Obj s Γ A → Tm Γ A
obj→tm V = var
obj→tm T = id

obj→tm≡ : ∀ {A} s (M : Obj s Γ A) → ⟦ obj→tm s M ⟧tm ≡ ⟦ M ⟧o
obj→tm≡ V M = refl
obj→tm≡ T M = refl

vzo : ∀ {Γ A} s → Obj s (Γ , A) (⟦ A ⟧T ∘ semwk _)
vzo V = vz
vzo T = var vz

vzo≡ : ∀ {Γ A} s → ⟦ vzo {Γ} {A} s ⟧o ≡ semvz
vzo≡ V = refl
vzo≡ T = refl

{-# REWRITE obj→tm≡ vzo≡ #-}

wko : ∀ {Γ B} s A → Obj s Γ B → Obj s (Γ , A) (B ∘ semwk _)
wko≡ : ∀ {Γ B} s A (M : Obj s Γ B) →  ⟦ wko s A M ⟧o ≡ ⟦ M ⟧o ∘ semwk _

wkos : ∀ A → Objs s Δ Γ → Objs s (Δ , A) Γ
wkos≡ : ∀ A (δ : Objs s Δ Γ) → ⟦ wkos A δ ⟧os ≡ ⟦ δ ⟧os ∘ semwk _

wkos A ε = ε
wkos A (_,_ {A = B} δ M) 
  = wkos A δ , subst (Obj _ _ ∘ (⟦ B ⟧T ∘_)) (sym (wkos≡ A δ)) (wko _ A M)

wkos≡ A ε = refl
wkos≡ {s = s} A (_,_ {A = B} δ M) 
  = dcong₂⁻¹ _,sub_ δ≡ (sym rm-subst 
  ∙ cong (subst (SemVal _ ∘ (⟦ B ⟧T ∘_)) (sym δ≡)) wkM≡)
  where δ≡ = wkos≡ A δ
        wkM≡ = wko≡ s A M
        rm-subst = subst-application′ (Obj s (_ , A) ∘ (⟦ B ⟧T ∘_)) (λ _ → ⟦_⟧o) 
                                      (sym δ≡)

wko* : ∀ (Γ′ : Tys Γ) → Objs s (Γ ++ Γ′) Γ
id-os : ∀ Γ → Objs s Γ Γ

wko*≡  : ∀ (Γ′ : Tys Γ) → ⟦ wko* {s = s} Γ′ ⟧os ≡ semwk* Γ′
id-os≡ : ∀ Γ → ⟦ id-os {s = s} Γ ⟧os ≡ id

id-os ε = ε
id-os (Γ , A) 
  = wkos _ idΓ 
  , subst (Obj _ _ ∘ (⟦ A ⟧T ∘_)) prf (vzo _)
  where idΓ = id-os Γ
        prf = cong (_∘ semwk ⟦ A ⟧T) (sym (id-os≡ _)) ∙ sym (wkos≡ A idΓ)

wko* ε = id-os _
wko* (Γ′ , A) = wkos _ (wko* Γ′)

wko*≡ ε = id-os≡ _
wko*≡ (Γ′ , A) = wkos≡ A (wko* Γ′) ∙ cong (_∘ semwk ⟦ A ⟧T) (wko*≡ Γ′)

id-os≡ ε = refl
id-os≡ {s = s} (Γ , A) 
  = dcong₂⁻¹ _,sub_ (wkos≡ A idΓ ∙ cong (_∘ semwk ⟦ A ⟧T) Γ≡) (sym rm-subst)
  where idΓ = id-os Γ
        Γ≡ = id-os≡ Γ
        prf = cong (_∘ semwk ⟦ A ⟧T) (sym (id-os≡ _)) ∙ sym (wkos≡ A idΓ)
        rm-subst = subst-application′ (Obj s (_ , A) ∘ (⟦ A ⟧T ∘_)) (λ _ → ⟦_⟧o) 
                                      prf

_[_]   : Ty Γ → Objs s Δ Γ → Ty Δ
_[_]tm : ∀ {Γ A} → Tm Γ A → (δ : Objs s Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧os)
_[_]v : ∀ {Γ A} → Var Γ A → (δ : Objs s Δ Γ) → Obj s Δ (A ∘ ⟦ δ ⟧os)

_[_]≡ : ∀ (A : Ty Γ) (δ : Objs s Δ Γ) → ⟦ A [ δ ] ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧os
_[_]tm≡ : ∀ {A} (M : Tm Γ A) → (δ : Objs s Δ Γ) 
        → ⟦ M [ δ ]tm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧os
_[_]v≡ : ∀ {A} (x : Var Γ A) → (δ : Objs s Δ Γ) 
       → ⟦ x [ δ ]v ⟧o ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧os

_↑os_ : ∀ (δ : Objs s Δ Γ) A → Objs s (Δ , A [ δ ]) (Γ , A)
δ ↑os A = wkos (A [ δ ]) δ , subst (Obj _ _) (cong (_∘ semwk _) A≡
        ∙ cong (⟦ A ⟧T ∘_) (sym (wkos≡ (A [ δ ]) δ))) (vzo _)
  where A≡ = A [ δ ]≡

_↑os≡_ : ∀ (δ : Objs s Δ Γ) A
     → ⟦ δ ↑os A ⟧os 
    ≡[ cong₂ SemSub (cong (_ ,s_ ) (A [ δ ]≡)) refl 
    ]≡ ⟦ δ ⟧os ↑s ⟦ A ⟧T
_↑os≡_ {s = s} δ A
  = from-coe≡⁻¹ _ (dcong₂⁻¹ _,sub_ wkδ≡ (sym rm-subst ∙ coes-cancel)
  ∙ sym (↑[]-helper ⟦ δ ⟧os A≡))
  where
    A≡ = A [ δ ]≡
    wkδ≡ = wkos≡ (A [ δ ]) δ
    prf = (cong (_∘ semwk ⟦ A [ δ ] ⟧T) A≡
        ∙ cong (⟦ A ⟧T ∘_) (sym (wkos≡ (A [ δ ]) δ)))
    rm-subst = subst-application′ (Obj s (_ , (A [ δ ]))) (λ _ → ⟦_⟧o) prf
    coes-cancel = sym (coe-coe semvz _ 
                      (cong (SemVal _ ∘ (_∘ semwk ⟦ A [ δ ] ⟧T)) A≡))

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

var x [ δ ]tm = obj→tm _ (x [ δ ]v)
app {B = B} M N [ δ ]tm 
  = subst (λ N[] → Tm _ (B ∘ (⟦ δ ⟧os ,sub N[]))) (N [ δ ]tm≡) 
          (app (M [ δ ]tm) (N [ δ ]tm))
lam {A = A} {B = B} M [ δ ]tm 
  = subst (Tm _) (dcong₂⁻¹ Πsem A≡ (cong (B ∘_) (to-coe≡⁻¹ _ (δ ↑os≡ A) 
  ∙ ↑[]-helper _ A≡ ∙ cong (_ ,sub_) (sym (semvz-helper A≡)))
  ∙ []-helper B ⟦ δ ⟧os A≡)) 
    (lam (M [ δ ↑os _ ]tm))
  where A≡ = A [ δ ]≡

var x [ δ ]tm≡ = x [ δ ]v≡
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

wk-poly : ∀ s → Objs s (Γ , A) Γ
wk-poly _ = wkos _ (id-os _)

wko V A = vs
wko {B = B} (T>V v _) A M 
  = subst (Tm (_ , A) ∘ (B ∘_)) 
          (wkos≡ A (id-os _) ∙ cong (_∘ semwk _) (id-os≡ _)) 
          (M [ wk-poly v ]tm)

wko≡ V A x = refl
wko≡ {B = B} T A M 
  = sym rm-subst 
  ∙ cong (subst (SemVal _ ∘ (B ∘_)) prf) 
         (M [ _ ]tm≡ ∙ dcong⁻¹ (⟦ M ⟧tm ∘_) prf) 
  ∙ coes-cancel
  where prf = wkos≡ A (id-os _) ∙ cong (_∘ semwk _) (id-os≡ _)
        rm-subst = subst-application′ (Tm (_ , A) ∘ (B ∘_)) (λ _ → ⟦_⟧tm) prf
        coes-cancel = coe-coe (⟦ M ⟧tm ∘ semwk ⟦ A ⟧T) 
                              (cong (SemVal _ ∘ (B ∘_)) prf) _

{-# REWRITE _[_]≡ _[_]tm≡ _[_]v≡ wko≡ wkos≡ wko*≡ id-os≡ #-}

wk : Vars (Γ , A) Γ
wk = wk-poly _

<_> : Tm Γ ⟦ A ⟧T → Tms Γ (Γ , A)
< M > = id-os _ , M
