open import Syntax
open import Nf
open import NoSub

open import Relation.Binary.PropositionalEquality using (_≡_; subst; refl)

module NbE where

-- Parallel substitutions:
data Subs : Ctx → Ctx → Set where
  id  : ∀ {Γ} → Subs Γ Γ
  _,_ : ∀ {Γ Δ Σ} → Sub Δ Γ → Subs Σ Δ → Subs Σ Γ

_[_]Tsubs : ∀ {Γ Δ} → Ty Γ → Subs Δ Γ → Ty Δ
_[_]subs  : ∀ {Γ Δ A} → Tm Γ A → (δ : Subs Δ Γ) → Tm Δ (A [ δ ]Tsubs)

_∘_ : ∀ {Γ Δ Σ} → Subs Δ Γ → Subs Σ Δ → Subs Σ Γ
id ∘ σ = σ
(δ , σ) ∘ γ = δ , (σ ∘ γ)

A [ id ]Tsubs = A
A [ δ , σ ]Tsubs = A [ δ ]T [ σ ]Tsubs

M [ id ]subs = M
M [ δ , σ ]subs = M [ δ ] [ σ ]subs

_↑s_ : ∀ {Γ Δ} (δ : Subs Γ Δ) A → Subs (Γ , (A [ δ ]Tsubs)) (Δ , A)
id ↑s A = id
(δ , σ) ↑s A = (δ ↑ A) , (σ ↑s (A [ δ ]T))

{-# NO_POSITIVITY_CHECK #-}
data Val : ∀ Γ A → Tm Γ A → Set where
  -- UVal  : ∀ {Γ M} → Ne Γ U M → Val Γ U
  -- ElVal : ∀ {Γ A M} → Ne Γ (El A) M → Val Γ (El A)
  ΠVal  : ∀ {Γ A B M} → (∀ {N} → Val Γ A N → Val Γ (B [ < N > ]T) (app M N)) 
        → Val Γ (Π A B) M

-- data Env : Ctx → Set

-- data Env where
--   ε   : Env ε
--   _,_ : ∀ {Γ} → (Δ : Env Γ) → 

app-val : ∀ {Γ A B M N} → Val Γ (Π A B) M → Val Γ A N → Val Γ _ (app M N)

⟦_⟧tm : ∀ {Γ Δ A M} → NsCoe Γ A M → (δ : Subs Δ Γ) → Val Δ (A [ δ ]Tsubs) (M [ δ ]subs)

⟦_⟧tm′ : ∀ {Γ Δ A M} → Ns Γ A M → (δ : Subs Δ Γ) → Val Δ (A [ δ ]Tsubs) (M [ δ ]subs)
⟦ var x ⟧tm′ = {!!}
⟦ app M N ⟧tm′ = {!!}
⟦ lam M ⟧tm′ δ = subst (λ x → x) {!!} (ΠVal (λ {N = N} x → subst (λ x → x) {!!} 
                 (⟦ M ⟧tm (< N > , id))))
-- (δ ↑s _) ∘ (< _ > , id)
-- (B [ ?3 ]T) ≡ ((B [ δ ↑ A ]T) [ < N > ]T)

-- data Vars : Ctx → Ctx → Set 

-- ⌜_⌝vs : ∀ {Γ Δ} → Vars Γ Δ → Subs Γ Δ
-- _[_]Tren : ∀ {Γ Δ} → Ty Γ → Vars Δ Γ → Ty Δ

-- data Vars where
--   ε   : ∀ {Γ} → Vars Γ ε
--   _,_ : ∀ {Γ Δ A} (δ : Vars Γ Δ) {x} → Var Γ (A [ ⌜ δ ⌝vs ]Tsubs) x 
--       → Vars Γ (Δ , A)

-- _[_]ren : ∀ {Γ Δ A} → Tm Γ A → (δ : Vars Δ Γ) → Tm Δ (A [ δ ]Tren) 

-- -- U [ δ ]Tren = U
-- -- El M [ δ ]Tren = El (M [ δ ]ren)
-- -- Π A B [ δ ]Tren = Π (A [ δ ]Tren) (B [ δ ↑ A ]Tren)

-- ⌜_⌝vs (ε {Γ = ε}) = id
-- ⌜_⌝vs (ε {Γ = (Γ , A)}) = ⌜ ε {Γ = Γ} ⌝vs ∘∘ (wk ∘ id)
-- ⌜ _,_ δ {x = x} _ ⌝vs = (⌜ δ ⌝vs ↑s _) ∘∘ (< x > ∘ id)

-- A [ δ ]Tren = A [ ⌜ δ ⌝vs ]Tsubs

-- M [ δ ]ren = M [ ⌜ δ ⌝vs ]subs

-- ⦅_⦆C : Ctx → Set 
-- ⦅ Γ ⦆C = {!!}

-- ⦅_⦆T : (Γ : Ctx) → ⦅ Γ ⦆C → Set 

-- -- qC : (Γ : Ctx) 
 