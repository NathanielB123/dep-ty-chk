{-# OPTIONS --prop --rewriting --show-irrelevant #-}

open import Coincidences.Utils
open import Coincidences.Equations
open import Coincidences.Bootstrap

module Coincidences.Bootstrap.Sub where

open import Coincidences.Sub 
  renaming (_[_]wtm to _[_]w◐tm; _[_]stm to _[_]s◐tm
  ; _[_]wv to _[_]w◐v; _[_]sv to _[_]s◐v
  ; _[_]wv≡ to _[_]w◐v≡; _[_]wtm≡ to _[_]w◐tm≡) 
  public
open import Coincidences.MSub
  renaming (_[_]tm to _[_]◐tm; _[_]v to _[_]◐v)
  public

↓tm-coe-lift : ∀ {Γ₁ Γ₂ A₁ A₂} {M : Tm Γ₁ A₁} (Γ≡ : Γ₁ ≡ Γ₂) 
                 (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
             → ↓tm (coe (Tm≡ Γ≡ A≡) M) ≡ coe (SemiTm≡ Γ≡ (⟦⟧T≡ Γ≡ A≡)) (↓tm M)
↓tm-coe-lift refl refl = refl

_[_]wtm : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]w)
_[_]wtm≡ : ∀ (M : Tm Γ A) (δ : Wk Δ Γ) → ↓tm (M [ δ ]wtm) ≡ (↓tm M) [ δ ]w◐tm
_[_]wv : Var Γ A → ∀ δ → Var Δ (A [ δ ]w)
_[_]wv≡ : ∀ (x : Var Γ A) (δ : Wk Δ Γ) → ↓v (x [ δ ]wv) ≡ (↓v x) [ δ ]w◐v


var x [ δ ]wtm = var (x [ δ ]wv)
app {B = B} M N p [ δ ]wtm 
  = subst (Tm _) (cong (B [ δ ↑ _ ]w [_]s ∘ <_>) (N [ δ ]wtm≡) 
                        ∙ sym (<>-comm-↑↑w ε _ refl)) 
          (app (M [ δ ]wtm) (N [ δ ]wtm) (cong (_∘ ⟦ δ ⟧w) p))
lam M [ δ ]wtm = lam (M [ δ ↑ _ ]wtm)

[]wtm-helper : ∀ {B} (p : ⟦ A ⟧T ≡ B) (M : Tm Γ A) (δ : Wk Δ Γ) 
       → subst (SemiTm Δ) (cong (_∘ ⟦ δ ⟧w) p) (↓tm M [ δ ]w◐tm) 
       ≡ subst (SemiTm Γ) p (↓tm M) [ δ ]w◐tm
[]wtm-helper refl _ _ = refl

var x [ δ ]wtm≡ = cong var (x [ δ ]wv≡)
app {A = A} {B = B} {ΠAB = ΠAB} M N p [ δ ]wtm≡
  = ↓tm-coe-lift refl prf ∙ to-coe≡ _ MN≡ 
  ∙ cong (λ M[] → app M[] (↓tm N [ δ ]w◐tm)) ([]wtm-helper p M δ)
  where
    A≡ = cong (_∘ ⟦ δ ⟧w) p
    M≡ = M [ δ ]wtm≡
    N≡ = N [ δ ]wtm≡
    prf = cong (B [ δ ↑ _ ]w [_]s ∘ <_>)  (N [ _ ]wtm≡)
        ∙ sym (<>-comm-↑↑w ε _ refl)
    MN≡ = app≡ refl refl refl (cong (subst (SemiTm _) A≡) M≡) N≡

lam M [ δ ]wtm≡ = cong lam (M [ δ ↑ _ ]wtm≡)

x [ wk ]wv = vs x 
vz [ δ ↑ A ]wv = vz 
vs x [ δ ↑ A ]wv = vs (x [ δ ]wv) 

x [ wk ]wv≡ = refl 
vz [ δ ↑ A ]wv≡ = refl
vs x [ δ ↑ A ]wv≡ = cong vs (x [ δ ]wv≡)

semwk* : ∀ {Γ} (Γ′ : SemTys Γ) → SemSub (Γ ++s Γ′) Γ
semwk* ε = id
semwk* (Γ′ , A) = semwk* Γ′ ∘ semwk A

wk* : (Γ′ : Tys Γ) → MSub (Γ ++ Γ′) Γ
wk* ε = idₛ
wk* (Γ′ , A) = wk* Γ′ ◂w wk

extend : (ρ : MSub Δ Γ) → SemiTm Δ (⟦ A ⟧T ∘ ⟦ ρ ⟧ms) → MSub Δ (Γ , A)
extend ρ M = (ρ ↑m _) ◂s < M >

build : Ctx → Tys ε
build≡ : ∀ Γ → ε ++ build Γ ≡ Γ

build ε = ε
build (Γ , A) = build Γ , subst Ty (sym (build≡ Γ)) A

build-helper : ∀ Γ Γ≡ 
             → (Γ , subst Ty (sym Γ≡) A)
             ≡ subst (λ z → Ty z → Ctx) Γ≡ (_,_ Γ) A
build-helper _ refl = refl

build≡ ε = refl
build≡ (Γ , A) = build-helper (ε ++ build Γ) Γ≡ ∙ cong-app (dcong Ctx._,_ Γ≡) A
  where Γ≡ = build≡ Γ

{-# REWRITE build≡ #-}

data Tms : Ctx → Ctx → Set
tmssub : Tms Δ Γ → MSub Δ Γ

data Tms where
  ε   : Tms Δ ε
  _,_ : ∀ ρ → SemiTm Δ (⟦ A ⟧T ∘ ⟦ tmssub ρ ⟧ms) → Tms Δ (Γ , A)

tmssub ε = wk* (build _)
tmssub (ρ , M) = extend (tmssub ρ) M

shift : ∀ A → Tys (Γ , A) → Tys Γ
shift≡ : ∀ (Γ′ : Tys (Γ , A)) → (Γ , A) ++ Γ′ ≡ Γ ++ shift A Γ′ 


shift A ε = ε , A
shift A (Γ′ , B) = shift A Γ′ , subst Ty (shift≡ Γ′) B

shift≡ ε = refl
shift≡ (Γ′ , A) = dcong₂ Ctx._,_ (shift≡ Γ′) refl

{-# REWRITE shift≡ #-}

pick : ∀ Γ′ → Var (Γ ++ shift A Γ′) (A [ wk* (shift A Γ′) ]) 
pick ε = vz
pick (Γ′ , _) = pick Γ′ [ wk ]wv

make-tms : ∀ Γ (Γ′ : Tys Γ) → Tms (Γ ++ Γ′) Γ

make-tms≡ : ∀ Γ (Γ′ : Tys Γ) → ⟦ tmssub (make-tms Γ Γ′) ⟧ms ≡ ⟦ wk* Γ′ ⟧ms

make-tms ε Γ′ = ε 
make-tms (Γ , A) Γ′ 
  = make-tms Γ (shift A Γ′) 
  , subst (SemiTm _) (cong (⟦ A ⟧T ∘_) (sym (make-tms≡ Γ (shift A Γ′)))) 
          (var (↓v (pick Γ′)))

-- TODO
make-tms≡ ε Γ′ = {!!}
make-tms≡ (Γ , A) Γ′ = {!!} ∙ waa ∙ {!!}
  where huh = make-tms≡ Γ (shift A Γ′)
        hmm = dcong (_↑s ⟦ A ⟧T) huh
        waa = cong (_∘ sem< ⟦ ↓v (pick Γ′) ⟧v >) hmm

id-tms : ∀ Γ → Tms Γ Γ
id-tms Γ = make-tms Γ ε
