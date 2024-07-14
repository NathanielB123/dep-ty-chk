{-# OPTIONS --rewriting --local-confluence-check #-}

import Agda.Builtin.Equality.Rewrite 

open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
  renaming (trans to _∙_)

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

infix 3 _≡[_]≡_

_≡[_]≡_ : ∀ {a} {A B : Set a} → A → A ≡ B → B → Set a
x ≡[ refl ]≡ y = x ≡ y

drefl : ∀ {a} {A : Set a} {x} (p : A ≡ A) → x ≡[ p ]≡ x
drefl refl = refl

-- Eventually I hope to replace most usages of this with rewrite rules that 
-- compute on the neutral equations (like ++≡β).
≡[]≡-uip : ∀ {a} {A B : Set a} {p q : A ≡ B} {x y} → x ≡[ p ]≡ y → x ≡[ q ]≡ y
≡[]≡-uip {p = refl} {q = refl} = id

_∙P_ : ∀ {a} {A B C D : Set a} {p : A ≡ B} {q : B ≡ C} {x y z} 
     → x ≡[ p ]≡ y → y ≡[ q ]≡ z → x ≡[ p ∙ q ]≡ z
_∙P_ {p = refl} {q = refl} refl refl = refl
