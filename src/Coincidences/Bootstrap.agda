{-# OPTIONS --rewriting --prop --show-irrelevant #-}
--local-confluence-check


open import Coincidences.Utils
open import Coincidences.Sub
open import Coincidences.Equations

-- With our lemmas about substitutions, we can now define terms indexed by
-- syntactic types, something which was impossible to get directly! I'm sure
-- using this technique has limitations, but this feels huge - intrinsically
-- typed syntax without quotients!
module Coincidences.Bootstrap where

open import Coincidences.Syntax 
  renaming (Var to SemiVar; Tm to SemiTm; Tm≡ to SemiTm≡; Var≡ to SemiVar≡) 
  public

wk-comm-↑w : ∀ {Γ Δ A} B {δ : Wk Δ Γ} 
           → B [ wk {A = A} ]w [ δ ↑ A ]w ≡ B [ δ ]w [ wk ]w
wk-comm-↑w A = wk-comm-↑↑w ε A refl


wk<>-id-↑ : ∀ {N} → B [ wk {A = A} ]w [ < N > ]s ≡ B
wk<>-id-↑ = wk<>-id-↑↑ ε _ refl

-- Proving this shouldn't be tricky, just need to do it...
postulate wkvz-id-↑ : B [ wk {A = A} ↑ A ]w [ < var vz > ]s ≡ B

{-# REWRITE wk-comm-↑w wk<>-id-↑ wkvz-id-↑ #-}

module TypeOf where
  type-of-v : ∀ {A} → SemiVar Γ A → Ty Γ
  type-of-v {Γ = _ , A} vz = A [ wk ]w
  type-of-v (vs x) = type-of-v x [ wk ]w

  type-of-v≡ : ∀ {A} (x : SemiVar Γ A) → ⟦ type-of-v x ⟧T ≡ A
  type-of-v≡ vz = refl
  type-of-v≡ (vs x) = cong (_∘ proj₁) (type-of-v≡ x)
open TypeOf

data Var : ∀ Γ → Ty Γ → Set
data Tm : ∀ Γ → Ty Γ → Set

↓v : Var Γ A → SemiVar Γ ⟦ A ⟧T 
↓tm : Tm Γ A → SemiTm Γ ⟦ A ⟧T

data Var where
  vz : Var (Γ , A) (A [ wk ]w)
  vs : Var Γ B → Var (Γ , A) (B [ wk ]w)
  -- We could relax how strict we are with how types should coincide to
  -- semantic equality here. I am actually not sure if this is necessary.
 
  -- vz : ∀ {Awk} → ⟦ A ⟧T ∘ semwk ⟦ A ⟧T ≡ ⟦ Awk ⟧T → Var (Γ , A) Awk
  -- vs : ∀ {Bwk} → Var Γ B → ⟦ B ⟧T ∘ semwk ⟦ A ⟧T ≡ ⟦ Bwk ⟧T 
  --              → Var (Γ , A) Bwk

data Tm where
   var : Var Γ A → Tm Γ A
   app : ∀ {Γ A} {B : Ty (Γ , A)} {ΠAB} → Tm Γ ΠAB 
       → (N : Tm Γ A) 
       → ⟦ ΠAB ⟧T ≡ Πsem ⟦ A ⟧T ⟦ B ⟧T
       → Tm Γ (B [ < ↓tm N > ]s)
   lam : Tm (Γ , A) B → Tm Γ (Π' A B)

private module Congruences where
  Var≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
       → Var Γ₁ A₁ ≡ Var Γ₂ A₂
  Var≡ refl refl = refl

  Tm≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
      → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂
  Tm≡ refl refl = refl
open Congruences public

↓v vz = vz
↓v (vs x) = vs (↓v x)

↓tm (var x)      = var (↓v x)
↓tm (app M N p)  = app (subst (SemiTm _) p (↓tm M)) (↓tm N)
↓tm (lam M)      = lam (↓tm M)

↑v : ∀ {A} (x : SemiVar Γ A) → Var Γ (type-of-v x) 
↑v vz = vz 
↑v (vs x) = vs (↑v x)
