{-# OPTIONS --rewriting --local-confluence-check #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; subst; sym; cong; dcong₂; subst-application′)
  renaming (trans to _∙_)
open import Function using (_∘_; id)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Coincidences.Utils
open import Coincidences.Syntax

module Coincidences.Sub where

data Sub : Ctx → Ctx → Set
⟦_⟧s : Sub Δ Γ → ⟦ Δ ⟧c → ⟦ Γ ⟧c
_[_] : Ty Γ → Sub Δ Γ → Ty Δ
_[_]≡ : ∀ A (δ : Sub Δ Γ) → ⟦ A [ δ ] ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧s

data Sub where
  wk  : Sub (Γ , A) Γ
  <_> : Tm Γ ⟦ A ⟧T → Sub Γ (Γ , A)
  _↑_ : ∀ δ A → Sub (Γ , A [ δ ]) (Δ , A)

⟦ wk ⟧s            = proj₁
⟦ < M > ⟧s ρ       = ρ , ⟦ M ⟧tm ρ
⟦ δ ↑ A ⟧s (ρ , M) = ⟦ δ ⟧s ρ , subst (λ AB → El (AB ρ)) (A [ δ ]≡) M

⊥' [ δ ] = ⊥'
(Π' A B) [ δ ] = Π' (A [ δ ]) (B [ δ ↑ A ])
El' A [ δ ] = El' {!!}

-- TODO: Simplify this proof
[]helper : ∀ {⟦A[δ]⟧} (B : Ty (Γ , A)) (δ : Sub Δ Γ) 
            (p : ⟦A[δ]⟧ ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧s) 
        → subst (λ A′ → Σ ⟦ Δ ⟧c (El ∘ A′) → U) (sym p)
          (λ where (ρ , x) → ⟦ B ⟧T (⟦ δ ⟧s ρ , x))
        ≡ (λ where (ρ , x) → ⟦ B ⟧T (⟦ δ ⟧s ρ , subst (λ AB → El (AB ρ)) p x))
[]helper B δ refl = refl

⊥' [ δ ]≡ = refl
Π' A B [ δ ]≡ 
  = cong (Πsem ⟦ A [ δ ] ⟧T) (B [ δ ↑ A ]≡)
  ∙ sym (dcong₂ Πsem (sym A≡) ([]helper B δ A≡))
  where A≡ = A [ δ ]≡
El' A [ δ ]≡ = refl

{-# REWRITE _[_]≡ #-}

_[_]tm : ∀ {A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧s)
_[_]tm≡ : ∀ {A} (M : Tm Γ A) (δ : Sub Δ Γ) 
        → ⟦ M [ δ ]tm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧s
_[_]v : ∀ {A} → Var Γ A → (δ : Sub Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧s)
_[_]v≡ : ∀ {A} (x : Var Γ A) (δ : Sub Δ Γ) 
        → ⟦ x [ δ ]v ⟧tm ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧s

x    [ wk    ]v = var (vs x)
vz   [ < M > ]v = M
vs x [ < M > ]v = var x
vz   [ δ ↑ A ]v = var vz
vs x [ δ ↑ A ]v = x [ δ ]v [ wk ]tm

x [ wk ]v≡ = refl
vz [ < M > ]v≡ = refl
vs x [ < M > ]v≡ = refl
vz [ δ ↑ A ]v≡ = refl
vs x [ δ ↑ A ]v≡ = {!x [ δ ]v≡!}

-- Todo implement this case in a terminating way by splitting subs and wks
var x [ δ ]tm = {!x [ δ ]v!}
app {B = B} M N [ δ ]tm 
  = subst (λ x → (Tm _ (λ ρ → B (⟦ δ ⟧s ρ , x ρ)))) 
          (N [ δ ]tm≡) (app (M [ δ ]tm) (N [ δ ]tm))
lam M [ δ ]tm = lam (M [ δ ↑ _ ]tm)

var x [ δ ]tm≡ = {!   !}
app {B = B} M N [ δ ]tm≡ 
  = sym (subst-application′ _ (λ _ → ⟦_⟧tm) (N [ δ ]tm≡)) 
  ∙ dcong-app (cong appsem (M [ δ ]tm≡)) (N [ δ ]tm≡)
lam M [ δ ]tm≡ = cong (λ M′ ρ → M′ ∘ (ρ ,_)) (M [ δ ↑ _ ]tm≡)
