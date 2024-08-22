{-# OPTIONS --prop --show-irrelevant --rewriting --local-confluence-check #-}

open import Coincidences.Utils
open import Coincidences.Syntax

-- Lists of types
module Coincidences.Tys where

data Tys : Ctx → Set
_++_ : ∀ Γ → Tys Γ → Ctx

data Tys where
  ε   : Tys Γ
  _,_ : ∀ Δ → Ty (Γ ++ Δ) → Tys Γ

Γ ++ ε       = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

-- Turn a context into a list of types
build : Ctx → Tys ε
build≡ : ∀ Γ → ε ++ build Γ ≡ Γ

build ε = ε
build (Γ , A) = build Γ , subst Ty (sym (build≡ Γ)) A

build≡ ε = refl
build≡ (Γ , A) = sym (dcong₂ _,_ (sym (build≡ Γ)) refl)

{-# REWRITE build≡ #-}

-- TODO: Put this in a more appropriate place
_↑s_ : ∀ {Γ Δ} (δ : SemSub Δ Γ) A → SemSub (Δ ,s (A ∘ δ)) (Γ ,s A)
_↑s_ δ A (ρ , x) = δ ρ , x
