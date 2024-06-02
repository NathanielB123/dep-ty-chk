{-# OPTIONS --prop #-}

module NewModular.PropUtils where

infixr 2 _∧_
infixr 1 _∨_

data ⊤ : Prop where tt : ⊤

data ⊥ : Prop where

record _∧_ (P Q : Prop) : Prop where
  constructor _,_
  eta-equality
  field
    proj₁ : P
    proj₂ : Q
open _∧_ public

data _∨_ (P Q : Prop) : Prop where
  inj₁ : P → P ∨ Q
  inj₂ : Q → P ∨ Q

∨-elim : ∀ {P Q} {R : Prop} → P ∨ Q → (P → R) → (Q → R) → R
∨-elim (inj₁ p) f g = f p
∨-elim (inj₂ q) f g = g q

-- Unclear if this variation is actually helpful at all
∨-depelim : ∀ {P Q} {R : P ∨ Q → Prop} (pq : P ∨ Q) 
        → (∀ p → R (inj₁ p)) → (∀ q → R (inj₂ q)) → R pq
∨-depelim (inj₁ p) f g = f p
∨-depelim (inj₂ q) f g = g q

data Squash (P : Set) : Prop where
  sq : P → Squash P

sq-elim : ∀ {P : Set} {Q : Prop} → Squash P → (P → Q) → Q
sq-elim (sq p) f = f p
