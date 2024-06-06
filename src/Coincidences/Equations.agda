{-# OPTIONS --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; subst)
  renaming (dcong to old)
-- I really did try to use indexed (Path-like) equality to try over 
-- heterogeneous, but it got too painful. Dependently-typed syntax is just too
-- dependent!
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; ≡-to-≅; ≅-to-≡; icong; icong₂)
  renaming (refl to hrefl; cong to hcong; cong₂ to hcong₂)
open import Function using (_∘_)

open import Coincidences.Syntax
open import Coincidences.Sub

module Coincidences.Equations where

dcong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
       → (p : x₁ ≡ x₂) → y₁ ≅ y₂
       → f x₁ y₁ ≡ f x₂ y₂
dcong₂ f refl hrefl = refl

infixl 100 _[_]tys

data Tys : Ctx → Set
_++_ : ∀ Γ → Tys Γ → Ctx

data Tys where
  ε   : Tys Γ
  _,_ : ∀ Δ → Ty (Γ ++ Δ) → Tys Γ

Γ ++ ε       = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

_[_]tys : Tys Γ → MSub Δ Γ → Tys Δ
_↑↑_ : ∀ (δ : MSub Δ Γ) Γ′ → MSub (Δ ++ Γ′ [ δ ]tys) (Γ ++ Γ′)

ε        [ δ ]tys = ε
(Γ′ , A) [ δ ]tys = (Γ′ [ δ ]tys) , (A [ δ ↑↑ Γ′ ])
      
δ ↑↑ ε = δ     
δ ↑↑ (Γ′ , A) = (δ ↑↑ Γ′) ↑m A 

⟨_⟩w : Wk Δ Γ → MSub Δ Γ
⟨ δ ⟩w = idₛ ◂w δ

⟨_⟩s : Sub Δ Γ → MSub Δ Γ
⟨ δ ⟩s = idₛ ◂s δ

<>-commutes-tys : ∀ {N} Γ′ 
                → Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys
<>-commutes↑↑ : ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N} B 
              → Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
              ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys
              → B [ ⟨ < N > ⟩s ↑↑ Γ′ ] [ δ ↑↑ Γ′ [ idₛ ◂s < N > ]tys ] 
              ≅ B [ (δ ↑m A) ↑↑ Γ′ ] 
                  [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]
<>-commutes↑↑-tm :  ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N B} (M : Tm _ B) 
              → Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
              ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys
              → M [ ⟨ < N > ⟩s ↑↑ Γ′ ]tm [ δ ↑↑ Γ′ [ idₛ ◂s < N > ]tys ]tm 
              ≅ M [ (δ ↑m A) ↑↑ Γ′ ]tm
                  [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]tm

<>-commutes-tys ε = refl
<>-commutes-tys (Γ′ , B) = dcong₂ _,_ Γ≡ (<>-commutes↑↑ Γ′ B Γ≡)
  where Γ≡ = <>-commutes-tys Γ′

<>-commutes↑↑ Γ′ ⊥' p = hcong (λ Δ′ → Ty.⊥' {_ ++ Δ′}) (≡-to-≅ p)
<>-commutes↑↑ Γ′ (Π' B₁ B₂) p 
  = icong₂ (Ty ∘ (_ ++_)) p Ty.Π' B₁≡ 
           (<>-commutes↑↑ (Γ′ , _) B₂ (dcong₂ _,_ p B₁≡))
  where B₁≡ = <>-commutes↑↑ Γ′ B₁ p
<>-commutes↑↑ Γ′ (El' B) p 
  = icong (λ x → Tm (_ ++ x) _) p Ty.El' {!!}

<>-commutes↑↑-tm Γ′ (var x) p = {!   !}
<>-commutes↑↑-tm Γ′ (app M N) p = {!   !}
<>-commutes↑↑-tm Γ′ (lam M) p = {!   !}

<>-commutes : ∀ {N} B → B [ < N > ]s [ δ ] ≡ B [ δ ↑m A ] [ < N [ δ ]tm > ]s
<>-commutes {δ = δ} B = ≅-to-≡ (<>-commutes↑↑ {δ = δ} ε B refl)
   
 