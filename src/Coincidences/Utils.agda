{-# OPTIONS --rewriting --local-confluence-check #-}

import Agda.Builtin.Equality.Rewrite 

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Coincidences.Utils where

dcong-app : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≡ g → ∀ {x y} → (p : x ≡ y) → subst B p (f x) ≡ g y
dcong-app refl refl = refl

-- We would get this for free with a Prop-valued identity type, but Agda's Prop
-- has skill issues
subst-uip : ∀ {a} {A : Set a} {x : A} (P : A → Set) (p : x ≡ x) (px : P x) 
          → subst P p px ≡ px
subst-uip _ refl _ = refl
{-# REWRITE subst-uip #-}
