open import 1Lab.1Lab.Type using (Type)
open import 1Lab.1Lab.Path using (PathP; _≡_)

module DepTyChk.CubicalUtils where

infix 4 _≡[_]≡_

_≡[_]≡_ : ∀ {a} {A B : Type a} → A → A ≡ B → B → Type a
x ≡[ p ]≡ y = PathP (λ i → p i) x y
