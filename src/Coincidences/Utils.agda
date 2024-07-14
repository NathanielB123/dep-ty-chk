{-# OPTIONS --rewriting --local-confluence-check --prop #-}

import Agda.Builtin.Equality.Rewrite 

module Coincidences.Utils where

open import Function using (_∘_; case_of_; id)
  public
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; subst; dcong₂; sym; erefl; cong-app; dcong
        ; subst-application′)
  renaming (trans to infixr 9 _∙_)
  public
open import Data.Product using (Σ; _,_; proj₁; proj₂) public
open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public

coe : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coe = subst id

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
infixr 9 _∙P_

_≡[_]≡_ : ∀ {a} {A B : Set a} → A → A ≡ B → B → Set a
x ≡[ refl ]≡ y = x ≡ y

drefl : ∀ {a} {A : Set a} {x} (p : A ≡ A) → x ≡[ p ]≡ x
drefl refl = refl

-- Eventually I hope to replace most usages of this with rewrite rules that 
-- compute on the neutral equations (like ++≡β).
≡[]≡-uip : ∀ {a} {A B : Set a} {p q : A ≡ B} {x y} → x ≡[ p ]≡ y → x ≡[ q ]≡ y
≡[]≡-uip {p = refl} {q = refl} = id

_∙P_ : ∀ {a} {A B C : Set a} {p : A ≡ B} {q : B ≡ C} {x y z} 
     → x ≡[ p ]≡ y → y ≡[ q ]≡ z → x ≡[ p ∙ q ]≡ z
_∙P_ {p = refl} {q = refl} refl refl = refl

to-coe≡ : ∀ {a} {A B : Set a} {p : A ≡ B} {x y} → x ≡[ p ]≡ y → coe p x ≡ y
to-coe≡ {p = refl} = id
 