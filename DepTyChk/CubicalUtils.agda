open import 1Lab.Type using (Type; lsuc)
open import 1Lab.Path 
  using (PathP; _≡_; coe0→1; refl; _∨_; _∧_; ~_; ap; subst; _∙_)
open import 1Lab.Path.Cartesian using (I-interp)
open import 1Lab.Path.Reasoning using (∙-cancelsl; ∙-cancelsr; ∙-eliml; ∙-elimr)

module DepTyChk.CubicalUtils where

infix 4 _≡[_]≡_

_≡[_]≡_ : ∀ {a} {A B : Type a} → A → A ≡ B → B → Type a
x ≡[ p ]≡ y = PathP (λ i → p i) x y

coe : ∀ {a} {A B : Type a} → A ≡ B → A → B
coe p = coe0→1 (λ i → p i)

-- Unordered sum type
data USum {ℓ} (A : Type ℓ) (B : Type ℓ) : Type (lsuc ℓ) where
  inl : A → USum A B
  inr : B → USum A B
  swap : ∀ {x y} AB → x ≡[ AB ]≡ y → inl x ≡ inr y

-- Like "ap", but f is given evidence that it's argument is either equal to the
-- LHS or RHS
funky-ap : ∀ {a b} {A : Type a} {B : A → Type b} {x y : A}
   → (p : x ≡ y) → (f : (z : A) → USum (z ≡ x) (z ≡ y) → B z) 
   → f x (inl refl) ≡[ (λ i → B (p i)) ]≡ f y (inr refl)
funky-ap {x = x} {y = y} p f i = f (p i) (swap pixy interp i)
  where
    pixy : (p i ≡ x) ≡ (p i ≡ y)
    pixy = ap (p i ≡_) p
    interp : (λ j → p (i ∧ ~ j)) ≡[ pixy ]≡ (λ j → p (i ∨ j))
    interp j k = p (I-interp j (i ∧ ~ k) (i ∨ k))

map-idx : ∀ {ℓ} {A B : Type ℓ} {x y} {p q : A ≡ B} 
        → x ≡[ p ]≡ y → p ≡ q → x ≡[ q ]≡ y
map-idx eq pq = subst (_ ≡[_]≡ _) pq eq

∙refl : ∀ {ℓ} {A : Type ℓ} {x y : A} {p : x ≡ y} → p ∙ refl ≡ p
∙refl = ∙-elimr refl

refl∙ : ∀ {ℓ} {A : Type ℓ} {x y : A} {p : x ≡ y} → refl ∙ p ≡ p
refl∙ = ∙-eliml refl

