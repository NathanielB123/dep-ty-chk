{-# OPTIONS --rewriting --local-confluence-check --prop #-}

module Coincidences.Utils where

open import Function using (_∘_; case_of_; id)
  public
open import Data.Product using (Σ; _,_; proj₁; proj₂) public
open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public

infix 3 _≡[_]≡_
infix 4 _≡_
infixr 9 _∙_
-- infixr 9 _∙P_

data _≡_ {a} {A : Set a} (x : A) : A → Prop a where
  refl : x ≡ x
{-# BUILTIN REWRITE _≡_ #-}

--------------------------------------------------------------------------------
-- Copied from Agda stdlib
--------------------------------------------------------------------------------

pattern erefl x = refl {x = x}

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_∙_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} 
          (f : A → B → C) {x y u v} → x ≡ y → u ≡ v 
      → f x u ≡ f y v
cong₂ f refl refl = refl

cong-app : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

subst-prop : ∀ {a b} {A : Set a} {x y} (P : A → Prop b) → x ≡ y → P x → P y
subst-prop P refl m = m

-- Agda's prop does not allow eliminating from Prop into Set, however, I believe
-- J for strict-prop-equality is reasonable along as we have K 
postulate
  subst  : ∀ {a b} {A : Set a} {x y} (P : A → Set b) → x ≡ y → P x → P y
  substβ : ∀ {a b} {A : Set a} {x} (P : A → Set b) (m : P x) 
         → subst P refl m ≡ m
{-# REWRITE substβ #-} 

dcong : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) {x y}
      → (p : x ≡ y) → subst B p (f x) ≡ f y
dcong f refl = refl

dcong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
       → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
       → f x₁ y₁ ≡ f x₂ y₂
dcong₂ f refl refl = refl

subst-application′ : ∀ {a b₁ b₂} {A : Set a}
                     (B₁ : A → Set b₁) {B₂ : A → Set b₂}
                     {x₁ x₂ : A} {y : B₁ x₁}
                     (g : ∀ x → B₁ x → B₂ x) (eq : x₁ ≡ x₂) →
                     subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ eq y)
subst-application′ _ _ refl = refl

--------------------------------------------------------------------------------

coe : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coe = subst id

coe-prop : ∀ {ℓ} {A B : Prop ℓ} → A ≡ B → A → B
coe-prop = subst-prop (λ x → x)

dcong-app : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≡ g → ∀ {x y} → (p : x ≡ y) → subst B p (f x) ≡ g y
dcong-app refl refl = refl

postulate 
  _≡[_]≡_ : ∀ {a} {A B : Set a} → A → A ≡ B → B → Prop a
  ≡[]≡β : ∀ {a} {A : Set a} {x y : A}
        → (x ≡[ refl ]≡ y) ≡ (x ≡ y)
{-# REWRITE ≡[]≡β #-} 

trans : ∀ {a} {A B C : Set a} (p : A ≡ B) (q : B ≡ C) {x y z} 
     → x ≡[ p ]≡ y → y ≡[ q ]≡ z → x ≡[ p ∙ q ]≡ z
trans refl refl refl refl = refl

to-coe≡ : ∀ {a} {A B : Set a} (p : A ≡ B) {x y} → x ≡[ p ]≡ y → coe p x ≡ y
to-coe≡ refl eq = eq
 
-- Sometimes, Agda will refuse to evaluate some Prop far enough (especially in
-- the presence of rewrite rules) and spurious type errors get thrown. 
-- It turns out that applying the identity function is usually enough to 
-- convince Agda that everything is ok.
[_]p : ∀ {ℓ} {A : Prop ℓ} → A → A
[ x ]p = x
