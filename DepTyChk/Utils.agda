open import 1Lab.1Lab.Path using (subst; transport-refl; refl; _≡_)
open import 1Lab.1Lab.Type using (Type)

module DepTyChk.Utils where

-- From Agda std-lib (I want to try and use both std-lib and 1Lab at once but
-- it appears this might be tricky due to 1Lab redefining primitives)

_∘_ : ∀ {a b c} {A : Type a} {B : A → Type b} {C : {x : A} → B x → Type c} 
    → (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) 
    → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

substRefl : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {x} → (px : B x) 
          → subst B refl px ≡ px
substRefl px = transport-refl px