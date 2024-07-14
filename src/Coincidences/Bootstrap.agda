{-# OPTIONS --rewriting --erasure #-}
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

↓v vz     = vz 
↓v (vs x) = vs (↓v x)

↓tm (var x)   = var (↓v x)
↓tm (app M N) = app (↓tm M) (↓tm N)
↓tm (lam M)   = lam (↓tm M)

Var≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
      → Var Γ₁ A₁ ≡ Var Γ₂ A₂
Var≡ refl refl = refl

Tm≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
    → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂
Tm≡ refl refl = refl

app≡′ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂ M₁ M₂ N₁ N₂} {Γ≡ : Γ₁ ≡ Γ₂}
          (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
          (B≡ : B₁ ≡[ Ty≡ (Γ≡ ,≡ A≡) ]≡ B₂) 
      → M₁ ≡[ Tm≡ Γ≡ (Π≡ A≡ B≡) ]≡ M₂
      → (N≡ : N₁ ≡[ Tm≡ Γ≡ A≡ ]≡ N₂)
      → app M₁ N₁ ≡[ Tm≡ Γ≡ ([]s≡ _ _ B≡ ({!!})) -- (sem<>≡ ⟦ Γ≡ ⟧c≡ A≡ (⟦⟧tm≡ Γ≡ A≡ N≡) B≡) 
    ]≡ app M₂ N₂
-- app≡′ refl refl refl refl refl = refl


_[_]wtm′ : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]w)
_[_]wtm≡′ : ∀ (M : Tm Γ A) (δ : Wk Δ Γ) → ↓tm (M [ δ ]wtm′) ≡ (↓tm M) [ δ ]wtm



var x [ δ ]wtm′ = {!   !} 
app {A = A} {B = B} M N [ δ ]wtm′ 
  = coe (Tm≡ refl (cong (B [ δ ↑ _ ]w [_]s ∘ <_>)  (N [ _ ]wtm≡′)
  ∙ sym (<>-comm-↑↑w ε _ refl))) 
    (app (M [ δ ]wtm′) (N [ δ ]wtm′))
lam M [ δ ]wtm′ = lam (M [ δ ↑ _ ]wtm′)

↓tm-coe-lift : ∀ {Γ₁ Γ₂ A₁ A₂} {M : Tm Γ₁ A₁} {Γ≡ : Γ₁ ≡ Γ₂} 
                 (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
             → ↓tm (coe (Tm≡ Γ≡ A≡) M) ≡ coe (PreTm≡ Γ≡ ⟦ A≡ ⟧T≡) (↓tm M)
↓tm-coe-lift {Γ≡ = refl} refl = refl

var x [ δ ]wtm≡′ = {!   !}
app {A = A} {B = B} M N [ δ ]wtm≡′ 
  = ↓tm-coe-lift prf ∙ {!!} ∙ to-coe≡ bruh
  where
    foo = M [ δ ]wtm≡′
    bar = N [ δ ]wtm≡′
    bruh = app≡ _ _ _ foo bar
    prf = cong (B [ δ ↑ _ ]w [_]s ∘ <_>)  (N [ _ ]wtm≡′)
        ∙ sym (<>-comm-↑↑w ε _ refl)
    -- car = app≡′ _ _ {!foo!} {!!}
lam M [ δ ]wtm≡′ = cong lam (M [ δ ↑ _ ]wtm≡′)
 