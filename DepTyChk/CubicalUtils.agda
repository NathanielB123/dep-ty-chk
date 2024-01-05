open import 1Lab.Type using (Type; lsuc)
open import 1Lab.Path 
  using (PathP; _≡_; transport; refl; _∨_; _∧_; ~_; ap; subst; _∙_; from-pathp
  ; transport-filler; transp; i0; i1; sym
  )
open import 1Lab.Path.Cartesian using (I-interp)
open import 1Lab.Path.Reasoning 
  using (∙-cancelsl; ∙-cancelsr; ∙-eliml; ∙-elimr; ∙-swapl; ∙-swapr)

module DepTyChk.CubicalUtils where

infix 4 _≡[_]≡_

_≡[_]≡_ : ∀ {a} {A B : Type a} → A → A ≡ B → B → Type a
x ≡[ p ]≡ y = PathP (λ i → p i) x y

coe : ∀ {a} {A B : Type a} → A ≡ B → A → B
coe = transport

-- Unordered sum type
data USum {ℓ} (A : Type ℓ) (B : Type ℓ) : Type (lsuc ℓ) where
  inl : A → USum A B
  inr : B → USum A B
  swap : ∀ {x y} AB → x ≡[ AB ]≡ y → inl x ≡ inr y

-- Like "ap", but f is given evidence that it's argument is either equal to the
-- LHS or RHS.
-- Unfortunately, this does not appear to be very helpful in practice, because
-- when matching on the evidence, we must ensure the boundary condition of swap
-- is obeyed, which requires showing the exact path we are trying to use 
-- funky-ap to prove...
-- I strongly feel that there should be some way to implement this sort of
-- function in a way that is actually helpful, but this ain't it.
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

subst₂ : ∀ {a b c} {A : Type a} {B : A → Type b} {x y u v} 
           (C : (x : A) → B x → Type c) (p : x ≡ y) 
       → u ≡[ ap B p ]≡ v → C x u → C y v
subst₂ C p q x = transp (λ i → C (p i) (q i)) i0 x


sym-inverts : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
sym-inverts _ = sym (∙-swapr (∙-eliml refl))

-- Thanks Naïm Favier!
subst-application : ∀ {a b c} {A : Type a}
                     (B : A → Type b) {C : A → Type c}
                     {x y : A} {z : B x}
                     (g : ∀ x → B x → C x) (p : x ≡ y) →
                     subst C p (g x z) ≡ g y (subst B p z)
subst-application B {C} {z = z} g p 
  = from-pathp λ i → g (p i) (transport-filler (ap B p) z i)
