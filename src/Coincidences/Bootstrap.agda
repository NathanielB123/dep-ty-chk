{-# OPTIONS --rewriting --prop --show-irrelevant #-}
--local-confluence-check

import Agda.Builtin.Equality.Rewrite

open import Coincidences.Utils
open import Coincidences.Sub
open import Coincidences.Equations

-- With our lemmas about substitutions, we can now define terms indexed by
-- syntactic types, something which was impossible to get directly! I'm sure
-- using this technique has limitations, but this feels huge - intrinsically
-- typed syntax without quotients!
module Coincidences.Bootstrap where

open import Coincidences.Syntax 
  renaming (Var to PreVar; Tm to PreTm; Tm≡ to PreTm≡; Var≡ to PreVar≡) 
  public

module TypeOf where
  type-of-v : ∀ {A} → PreVar Γ A → Ty Γ
  type-of-v {Γ = _ , A} vz = A [ wk ]w
  type-of-v (vs x) = type-of-v x [ wk ]w

  type-of-v≡ : ∀ {A} (x : PreVar Γ A) → ⟦ type-of-v x ⟧T ≡ A
  type-of-v≡ vz = refl
  type-of-v≡ (vs x) = cong (_∘ proj₁) (type-of-v≡ x)
open TypeOf

data Var : ∀ Γ → Ty Γ → Set
data Tm : ∀ Γ → Ty Γ → Set
↓v : Var Γ A → PreVar Γ ⟦ A ⟧T 
↓tm : Tm Γ A → PreTm Γ ⟦ A ⟧T

data Var where
  vz : Var (Γ , A) (A [ wk ]w)
  vs : Var Γ B → Var (Γ , A) (B [ wk ]w)

data Tm where
   var : Var Γ A → Tm Γ A
   -- Note that on-the-nose coincidence of types here is probably too strong
   -- given syntactic types are not necessarily in normal form
   -- We could relax this to ⟦ A₁ ⟧T ≡ ⟦ A₂ ⟧T...
   app : Tm Γ (Π' A B) → (N : Tm Γ A) → Tm Γ (B [ < ↓tm N > ]s)
   lam : Tm (Γ , A) B → Tm Γ (Π' A B)

private module Congruences where
  Var≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
       → Var Γ₁ A₁ ≡ Var Γ₂ A₂
  Var≡ refl refl = refl

  Tm≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
      → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂
  Tm≡ refl refl = refl
open Congruences public

↓v vz     = vz 
↓v (vs x) = vs (↓v x)

↓tm (var x)   = var (↓v x)
↓tm (app M N) = app (↓tm M) (↓tm N)
↓tm (lam M)   = lam (↓tm M)

↓tm-coe-lift : ∀ {Γ₁ Γ₂ A₁ A₂} {M : Tm Γ₁ A₁} (Γ≡ : Γ₁ ≡ Γ₂) 
                 (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
             → ↓tm (coe (Tm≡ Γ≡ A≡) M) ≡ coe (PreTm≡ Γ≡ (⟦⟧T≡ Γ≡ A≡)) (↓tm M)
↓tm-coe-lift refl refl = refl

_[_]wtm′ : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]w)
_[_]wtm≡′ : ∀ (M : Tm Γ A) (δ : Wk Δ Γ) → ↓tm (M [ δ ]wtm′) ≡ (↓tm M) [ δ ]wtm

var x [ δ ]wtm′ = {!   !} 
app {B = B} M N [ δ ]wtm′ 
  = coe (Tm≡ refl (cong (B [ δ ↑ _ ]w [_]s ∘ <_>)  (N [ _ ]wtm≡′)
  ∙ sym (<>-comm-↑↑w ε _ refl))) 
    (app (M [ δ ]wtm′) (N [ δ ]wtm′))
lam M [ δ ]wtm′ = lam (M [ δ ↑ _ ]wtm′)

var x [ δ ]wtm≡′ = {!   !}
app {B = B} M N [ δ ]wtm≡′ 
  = ↓tm-coe-lift refl prf ∙ to-coe≡ MN-i≡ MN≡
  where
    M≡ = M [ δ ]wtm≡′
    N≡ = N [ δ ]wtm≡′
    MN≡ = app≡ refl refl refl M≡ N≡
    prf = cong (B [ δ ↑ _ ]w [_]s ∘ <_>)  (N [ _ ]wtm≡′)
        ∙ sym (<>-comm-↑↑w ε _ refl)
    MN-i≡ = PreTm≡ refl (⟦⟧T≡ refl prf)
lam M [ δ ]wtm≡′ = cong lam (M [ δ ↑ _ ]wtm≡′)
  