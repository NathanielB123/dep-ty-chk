{-# OPTIONS --without-K #-}
-- {-# OPTIONS --show-implicit #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  renaming (sym to ≡sym)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using () renaming (_,_ to infixl 6 _,_)

open import Syntax

module EqUtils where

infix 4 _≈Maybe[_]_
infix 4 _≋Σ[_]_ 

collapse* : ∀ {C} {R : Rel C} {A B} {x : inter A} {y : inter B} 
          → *SymClosure (*SymClosure R) x y → *SymClosure R x y
collapse* rfl = rfl
collapse* (trs (p  ¹) r) = p ∙ collapse* r
collapse* (trs (p ⁻¹) r) = sym p ∙ collapse* r

data via_,_≋Maybe_ {C} (R : Rel C) 
                 : Rel (maybe C) where
  just    : ∀ {A B} {x : inter A} {y : inter B} → R x y 
          → via R , just x ≋Maybe just y
  nothing : ∀ {A B} → via R , nothing {A = inter A} ≋Maybe nothing {A = inter B}

_≈Maybe[_]_ : ∀ {C} {A B} → Maybe (inter A) → Rel C → Maybe (inter B) → Set
x ≈Maybe[ R ] y = *SymClosure (via R ,_≋Maybe_) x y

mapInv : ∀ {C} {R : Rel C} {A B} {f : inter A → inter B} → (∀ {x} → R (f x) x) 
        → {x : Maybe (inter A)} → via R , map f x ≋Maybe x
mapInv {f = f} p {x = just _}  = just p
mapInv {f = f} p {x = nothing} = nothing

just-inj : ∀ {C} {R : Rel C} {A B} {x : inter A} {y : inter B} 
         → just x ≈Maybe[ R ] just y → *SymClosure R x y
just-inj rfl = rfl
just-inj (trs (just p  ¹) r) = ⟦ p ⟧ ∙ just-inj r
just-inj (trs (just p ⁻¹) r) = ⟦ p ⟧⁻¹ ∙ just-inj r

_≋Σ[_]_ : ∀ {C₁ C₂} {A B} 
        → inter {exists C₁ C₂} A → Rel C₂ → inter {exists C₁ C₂} B → Set
(_ , x) ≋Σ[ R ] (_ , y) = R x y

collapseΣ* : ∀ {C₁ C₂} {R : Rel C₂} {A B} 
               {x : inter {exists C₁ C₂} A} {y : inter {exists C₁ C₂} B} 
           → *SymClosure (_≋Σ[ *SymClosure R ]_) x y → x ≋Σ[ *SymClosure R ] y
collapseΣ* rfl = rfl
collapseΣ* (trs (p ¹) r) = p ∙ collapseΣ* r
collapseΣ* (trs (p ⁻¹) r) = sym p ∙ collapseΣ* r
