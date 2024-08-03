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

-- Move a type from the end of a context to the start of a list of types
shift : ∀ A → Tys (Γ , A) → Tys Γ
shift≡ : ∀ (Γ′ : Tys (Γ , A)) → Γ ++ shift A Γ′ ≡ (Γ , A) ++ Γ′

shift A ε = ε , A
shift A (Γ′ , B) = shift A Γ′ , subst Ty (sym (shift≡ Γ′)) B

shift≡ ε = refl
shift≡ (Γ′ , A) = sym (dcong₂ _,_ (sym (shift≡ Γ′)) refl)

-- Turn a context into a list of types
build : Ctx → Tys ε
build≡ : ∀ Γ → ε ++ build Γ ≡ Γ

build ε = ε
build (Γ , A) = build Γ , subst Ty (sym (build≡ Γ)) A

build≡ ε = refl
build≡ (Γ , A) = sym (dcong₂ _,_ (sym (build≡ Γ)) refl)

{-# REWRITE shift≡ build≡ #-}

-- TODO: Put this in a more appropriate place
_↑s_ : ∀ {Γ Δ} (δ : SemSub Δ Γ) A → SemSub (Δ ,s (A ∘ δ)) (Γ ,s A)
_↑s_ δ A (ρ , x) = δ ρ , x
