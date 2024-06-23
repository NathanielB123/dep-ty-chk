{-# OPTIONS --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; subst; dcong₂; sym)
  renaming (trans to _∙_)
open import Function using (_∘_; case_of_; id)
open import Data.Product using (_,_; proj₁; proj₂)

open import Coincidences.Syntax
open import Coincidences.Sub

module Coincidences.Equations where

infix 3 _≡[_]≡_

_≡[_]≡_ : ∀ {a} {A B : Set a} → A → A ≡ B → B → Set a
x ≡[ refl ]≡ y = x ≡ y

drefl : ∀ {a} {A : Set a} {x} (p : A ≡ A) → x ≡[ p ]≡ x
drefl refl = refl

≡[]≡-irrev : ∀ {a} {A B : Set a} {p q : A ≡ B} {x y} → x ≡[ p ]≡ y → x ≡[ q ]≡ y
≡[]≡-irrev {p = refl} {q = refl} = id

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

Ty≡ = cong Ty
Tys≡ = cong Tys

SemTy≡ = cong SemTy
⟦_⟧c≡ = cong ⟦_⟧c 

module Congruence where
  Tm≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂) 
      → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂
  Tm≡ refl refl = refl

  _,≡_ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
      → (Ctx._,_ Γ₁ A₁) ≡ (Ctx._,_ Γ₂ A₂)
  refl ,≡ refl = refl

  _++≡_ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′} (Γ≡ : Γ₁ ≡ Γ₂) → Γ₁′ ≡[ cong Tys Γ≡ ]≡ Γ₂′
        → Γ₁ ++ Γ₁′ ≡ Γ₂ ++ Γ₂′
  refl ++≡ refl = refl

  ,tys≡ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) 
            (Γ≡′ : Γ₁′ ≡[ cong Tys Γ≡ ]≡ Γ₂′)
        → A₁ ≡[ Ty≡ (Γ≡ ++≡ Γ≡′) ]≡ A₂ → Γ₁′ , A₁ ≡[ Tys≡ Γ≡ ]≡ Γ₂′ , A₂ 
  ,tys≡ refl refl refl = refl

  ++≡β : ∀ {Γ} {Γ₁′ Γ₂′ : Tys Γ} {A₁ A₂} 
          (p : Γ₁′ ≡ Γ₂′) (q : A₁ ≡[ Ty≡ (refl ++≡ p) ]≡ A₂) 
      → refl ++≡ ,tys≡ refl p q ≡ (refl ++≡ p) ,≡ q
  ++≡β refl refl = refl

  {-# REWRITE ++≡β #-}

  Π≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
    → B₁ ≡[ Ty≡ (Γ≡ ,≡ A≡) ]≡ B₂ → Π' A₁ B₁ ≡[ Ty≡ Γ≡ ]≡ Π' A₂ B₂
  Π≡ refl refl refl = refl

  _,s≡_ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) → A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂ 
        → Γ₁ ,s A₁ ≡ Γ₂ ,s A₂
  refl ,s≡ refl = refl 

  Πsem≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂) 
        → B₁ ≡[ SemTy≡ (Γ≡ ,s≡ A≡) ]≡ B₂ 
        → Πsem A₁ B₁ ≡[ SemTy≡ Γ≡ ]≡ Πsem A₂ B₂
  Πsem≡ refl refl refl = refl

  ⟦⟧T≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) → A₁ ≡[ Ty≡ Γ≡ ]≡ A₂ 
      → ⟦ A₁ ⟧T ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ ⟦ A₂ ⟧T
  ⟦⟧T≡ refl refl = refl

  ⟦⟧c≡β : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
        → cong ⟦_⟧c (Γ≡ ,≡ A≡) ≡ ⟦ Γ≡ ⟧c≡ ,s≡ ⟦⟧T≡ Γ≡ A≡
  ⟦⟧c≡β refl refl = refl

  {-# REWRITE ⟦⟧c≡β #-}

  lam≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂ M₁ M₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
          (B≡ : B₁ ≡[ SemTy≡ ⟦ Γ≡ ,≡ A≡ ⟧c≡ ]≡ B₂) 
          (M≡ : M₁ ≡[ Tm≡ (Γ≡ ,≡ A≡) B≡ ]≡ M₂) 
      → lam M₁ ≡[ Tm≡ Γ≡ (Πsem≡ ⟦ Γ≡ ⟧c≡ (⟦⟧T≡ Γ≡ A≡) B≡) ]≡ lam M₂
  lam≡ refl refl refl refl = refl
open Congruence public

<>-commutes-tys : ∀ {N} Γ′ 
                → Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
                ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys
<>-commutes↑↑ : ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N} B 
                  (p : Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
                     ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys)
              → B [ ⟨ < N > ⟩s ↑↑ Γ′ ] [ δ ↑↑ Γ′ [ idₛ ◂s < N > ]tys ] 
             ≡[ Ty≡ (refl ++≡ p)
             ]≡ B [ (δ ↑m A) ↑↑ Γ′ ] [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]

<>-commutes-tys ε = refl
<>-commutes-tys (Γ′ , B) = ,tys≡ refl Γ≡′ (<>-commutes↑↑ Γ′ B Γ≡′)
  where Γ≡′ = <>-commutes-tys Γ′

<>-commutes↑↑ Γ′ ⊥' p = {!!}
<>-commutes↑↑ Γ′ (Π' B₁ B₂) p 
  = Π≡ (refl ++≡ p) B₁≡ B₂≡
  where B₁≡ = <>-commutes↑↑ Γ′ B₁ p
        B₂≡ = <>-commutes↑↑ (Γ′ , B₁) B₂ (,tys≡ refl p B₁≡)
<>-commutes↑↑ Γ′ (El' B) p = {!!}

<>-commutes-sem : ∀ {Γ Δ} {δ : MSub Δ Γ} {A} {N : Tm Γ ⟦ A ⟧T} 
                    (B : SemTy (⟦ Γ ⟧c ,s ⟦ A ⟧T))
              → B [ ⟨ <_> {A = A} N ⟩s ]sem [ δ ]sem 
              ≡ B [ δ ↑m A ]sem [ ⟨ <_> {A = A [ δ ]} (N [ δ ]tm) ⟩s ]sem
<>-commutes-sem {δ = δ} B = refl

-- This is really frustrating - every concrete case of this proof (for finite
-- Γ′s) is trivial, but I can't seem to prove it inductively?
<>-commutes↑↑-sem : ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N} B 
                      (p : Γ′ [ ⟨ < N > ⟩s ]tys [ δ ]tys 
                         ≡ Γ′ [ δ ↑m A ]tys [ ⟨ < N [ δ ]tm > ⟩s ]tys)
                  → B [ ⟨ < N > ⟩s ↑↑ Γ′ ]sem [ δ ↑↑ Γ′ [ idₛ ◂s < N > ]tys ]sem 
                 ≡[ SemTy≡ ⟦ refl ++≡ p ⟧c≡
                 ]≡ B [ (δ ↑m A) ↑↑ Γ′ ]sem
                      [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]sem
<>-commutes↑↑-sem ε B refl = refl
<>-commutes↑↑-sem (ε , A) B p = drefl _
<>-commutes↑↑-sem ((ε , A) , C) B p = drefl _
<>-commutes↑↑-sem (((ε , A) , C) , D) B p = drefl _
<>-commutes↑↑-sem (Γ′ , A) B p = {!   !}
  where ind = <>-commutes↑↑-sem Γ′ (λ x → B (x , {!!})) {!!}

<>-commutes↑↑-tm :  ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N B} (M : Tm _ B) 
                      (p : Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
                         ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys)
                 → M [ ⟨ < N > ⟩s ↑↑ Γ′ ]tm [ δ ↑↑ Γ′ [ idₛ ◂s < N > ]tys ]tm 
                ≡[ Tm≡ (refl ++≡ p) (<>-commutes↑↑-sem Γ′ B p)
                ]≡ M [ (δ ↑m A) ↑↑ Γ′ ]tm
                     [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]tm
<>-commutes↑↑-tm Γ′ (var x) p = {!   !}
<>-commutes↑↑-tm Γ′ (app M N) p = {!   !}
-- Interesting - the substitutions are not reducing in the goal type here
-- I'm not sure why... feels like a bug with Agda?
<>-commutes↑↑-tm {δ = δ} Γ′ {N = N} (lam {A = A} {B = B} M) p 
  = {!≡[]≡-irrev foo!} 
  where
    A≡ = <>-commutes↑↑ Γ′ A p 
    B≡ = <>-commutes↑↑-sem (Γ′ , A) B (,tys≡ refl p A≡)
    M≡ = <>-commutes↑↑-tm (Γ′ , A) M (,tys≡ refl p A≡)
    foo = lam≡ (_ ++≡ p) A≡ B≡ M≡
    -- Surely this *should* be provable with refl - lam[] is a rewrite rule!
    why-no-β : lam (M [ ((idₛ ◂s < N >) ↑↑ Γ′) ↑m A ]tm) 
                      [ δ ↑↑ (Γ′ [ idₛ ◂s < N > ]tys) ]tm
             ≡ lam (M [ ((idₛ ◂s < N >) ↑↑ Γ′) ↑m A ]tm 
                      [ (δ ↑↑ (Γ′ [ idₛ ◂s < N > ]tys)) 
                           ↑m A [ ((idₛ ◂s < N >) ↑↑ Γ′) ] ]tm)  
    why-no-β = lam[] {M = M [ ((idₛ ◂s < N >) ↑↑ Γ′) ↑m A ]tm} 
                     (δ ↑↑ (Γ′ [ idₛ ◂s < N > ]tys))
            
-- <>-commutes↑↑-tm :  ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N B} (M : Tm _ B) 
--               → Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
--               ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys
--               → M [ ⟨ < N > ⟩s ↑↑ Γ′ ]tm [ δ ↑↑ Γ′ [ idₛ ◂s < N > ]tys ]tm 
--               ≅ M [ (δ ↑m A) ↑↑ Γ′ ]tm
--                   [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]tm
-- <>-commutes↑↑-v :  ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N B} (x : Var _ B) 
--               → Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
--               ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys
--               → x [ ⟨ < N > ⟩s ↑↑ Γ′ ]v [ δ ↑↑ Γ′ [ idₛ ◂s < N > ]tys ]tm 
--               ≅ x [ (δ ↑m A) ↑↑ Γ′ ]v
--                   [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]tm

-- <>-commutes-tm :  ∀ {Γ Δ} (δ : MSub Δ Γ) {A} {N B} (M : Tm _ B) 
--               → M [ ⟨ < N > ⟩s ]tm [ δ ]tm 
--               ≡ M [ δ ↑m A ]tm [ ⟨ < N [ δ ]tm > ⟩s ]tm

-- <>-commutes-v :  ∀ {Γ Δ} (δ : MSub Δ Γ) {A} {N B} (x : Var _ B) 
--               → x [ ⟨ < N > ⟩s ]v [ δ ]tm 
--               ≡ x [ δ ↑m A ]v [ ⟨ < N [ δ ]tm > ⟩s ]tm
