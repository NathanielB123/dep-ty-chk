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

mwk : ∀ Γ′ → MSub (Γ ++ Γ′) Γ
mwk ε = idₛ
mwk (Γ′ , A) = mwk Γ′ ◂w wk

module Congruences where
  Ty≡ = cong Ty
  Tys≡ = cong Tys

  SemTy≡ = cong SemTy
  ⟦_⟧c≡ = cong ⟦_⟧c 

  SemSub≡ = cong₂ SemSub

  Tm≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂) 
      → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂
  Tm≡ refl refl = refl

  _,≡_ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
      → (Ctx._,_ Γ₁ A₁) ≡ (Ctx._,_ Γ₂ A₂)
  refl ,≡ refl = refl

  _++≡_ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′} (Γ≡ : Γ₁ ≡ Γ₂) → Γ₁′ ≡[ Tys≡ Γ≡ ]≡ Γ₂′
        → Γ₁ ++ Γ₁′ ≡ Γ₂ ++ Γ₂′
  refl ++≡ refl = refl

  ,tys≡ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) 
            (Γ≡′ : Γ₁′ ≡[ Tys≡ Γ≡ ]≡ Γ₂′)
        → A₁ ≡[ Ty≡ (Γ≡ ++≡ Γ≡′) ]≡ A₂ → Γ₁′ , A₁ ≡[ Tys≡ Γ≡ ]≡ Γ₂′ , A₂ 
  ,tys≡ refl refl refl = refl

  ++≡β : ∀ {Γ} {Γ₁′ Γ₂′ : Tys Γ} {A₁ A₂} 
          (p : Γ₁′ ≡ Γ₂′) (q : A₁ ≡[ Ty≡ (refl ++≡ p) ]≡ A₂) 
      → refl ++≡ ,tys≡ refl p q ≡ (refl ++≡ p) ,≡ q
  ++≡β refl refl = refl

  {-# REWRITE ++≡β #-}

  ⟦⟧T≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) → A₁ ≡[ Ty≡ Γ≡ ]≡ A₂ 
       → ⟦ A₁ ⟧T ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ ⟦ A₂ ⟧T
  ⟦⟧T≡ refl refl = refl

  ⊥≡ : ∀ {Γ₁ Γ₂} (Γ≡ : Γ₁ ≡ Γ₂) → ⊥' ≡[ Ty≡ Γ≡ ]≡ ⊥'
  ⊥≡ refl = refl

  Π≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
    → B₁ ≡[ Ty≡ (Γ≡ ,≡ A≡) ]≡ B₂ → Π' A₁ B₁ ≡[ Ty≡ Γ≡ ]≡ Π' A₂ B₂
  Π≡ refl refl refl = refl

  El≡ : ∀ {Γ₁ Γ₂ M₁ M₂} (Γ≡ : Γ₁ ≡ Γ₂)
      → M₁ ≡[ Tm≡ Γ≡ (⟦⟧T≡ Γ≡ (⊥≡ Γ≡)) ]≡ M₂
      → El' M₁ ≡[ Ty≡ Γ≡ ]≡ El' M₂
  El≡ refl refl = refl

  _,s≡_ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) → A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂ 
        → Γ₁ ,s A₁ ≡ Γ₂ ,s A₂
  refl ,s≡ refl = refl 

  Πsem≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂) 
        → B₁ ≡[ SemTy≡ (Γ≡ ,s≡ A≡) ]≡ B₂ 
        → Πsem A₁ B₁ ≡[ SemTy≡ Γ≡ ]≡ Πsem A₂ B₂
  Πsem≡ refl refl refl = refl

  ⟦⟧c≡β : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
        → cong ⟦_⟧c (Γ≡ ,≡ A≡) ≡ ⟦ Γ≡ ⟧c≡ ,s≡ ⟦⟧T≡ Γ≡ A≡
  ⟦⟧c≡β refl refl = refl

  {-# REWRITE ⟦⟧c≡β #-}

  lam≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂ M₁ M₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
          (B≡ : B₁ ≡[ SemTy≡ ⟦ Γ≡ ,≡ A≡ ⟧c≡ ]≡ B₂) 
          (M≡ : M₁ ≡[ Tm≡ (Γ≡ ,≡ A≡) B≡ ]≡ M₂) 
      → lam M₁ ≡[ Tm≡ Γ≡ (Πsem≡ ⟦ Γ≡ ⟧c≡ (⟦⟧T≡ Γ≡ A≡) B≡) ]≡ lam M₂
  lam≡ refl refl refl refl = refl

  ,proj≡₁ : ∀ {Γ Γ₁′ Γ₂′} {A₁ : Ty (Γ ++ Γ₁′)} {A₂ : Ty (Γ ++ Γ₂′)} 
          → Tys._,_ Γ₁′ A₁ ≡ Tys._,_ Γ₂′ A₂ → Γ₁′ ≡ Γ₂′
  ,proj≡₁ refl = refl

  []sem≡ : ∀ {Γ₁ Γ₂ Δ δ₁ δ₂} (A : SemTy Δ) (Γ≡ : Γ₁ ≡ Γ₂) 
      → δ₁ ≡[ SemSub≡ Γ≡ refl ]≡ δ₂ 
      → A ∘ δ₁ ≡[ cong (λ Γ → Γ → U) Γ≡ ]≡ A ∘ δ₂
  []sem≡ _ refl refl = refl

  ↑sem≡ : ∀ {Γ₁ Γ₂ Δ δ₁ δ₂} {A : SemTy Δ} (Γ≡ : Γ₁ ≡ Γ₂)
            (δ≡ : δ₁ ≡[ SemSub≡ Γ≡ refl ]≡ δ₂) 
        → δ₁ ↑sem A ≡[ SemSub≡ (Γ≡ ,s≡ ([]sem≡ A Γ≡ δ≡)) refl ]≡ δ₂ ↑sem A
  ↑sem≡ refl refl = refl

open Congruences public

<>-commutes-tys : ∀ {N} Γ′ 
                → Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
                ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys
<>-commutes↑↑ : ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N} B 
                  (p : Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
                     ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys)
              → B [ ⟨ < N > ⟩s ↑↑ Γ′ ] [ δ ↑↑ Γ′ [ idₛ ◂s < N > ]tys ] 
             ≡[ Ty≡ (refl ++≡ p)
             ]≡ B [ (δ ↑m A) ↑↑ Γ′ ] [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]
<>-commutes↑↑-sem : ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N} B 
                      (p : Γ′ [ ⟨ < N > ⟩s ]tys [ δ ]tys 
                         ≡ Γ′ [ δ ↑m A ]tys [ ⟨ < N [ δ ]tm > ⟩s ]tys)
                  → B [ ⟨ < N > ⟩s ↑↑ Γ′ ]sem [ δ ↑↑ Γ′ [ ⟨ < N > ⟩s ]tys ]sem 
                 ≡[ SemTy≡ ⟦ refl ++≡ p ⟧c≡
                 ]≡ B [ (δ ↑m A) ↑↑ Γ′ ]sem
                      [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]sem
<>-commutes↑↑-tm :  ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N B} (M : Tm _ B) 
                      (p : Γ′ [ idₛ ◂s < N > ]tys [ δ ]tys 
                         ≡ Γ′ [ δ ↑m A ]tys [ idₛ ◂s < N [ δ ]tm > ]tys)
                 → M [ ⟨ < N > ⟩s ↑↑ Γ′ ]tm [ δ ↑↑ Γ′ [ idₛ ◂s < N > ]tys ]tm 
                ≡[ Tm≡ (refl ++≡ p) (<>-commutes↑↑-sem Γ′ B p)
                ]≡ M [ (δ ↑m A) ↑↑ Γ′ ]tm
                     [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]tm

<>-commutes-tys ε = refl
<>-commutes-tys (Γ′ , B) = ,tys≡ refl Γ≡′ (<>-commutes↑↑ Γ′ B Γ≡′)
  where Γ≡′ = <>-commutes-tys Γ′

<>-commutes↑↑ Γ′ ⊥' p = ⊥≡ (refl ++≡ p)
<>-commutes↑↑ Γ′ (Π' B₁ B₂) p 
  = Π≡ (refl ++≡ p) B₁≡ B₂≡
  where B₁≡ = <>-commutes↑↑ Γ′ B₁ p
        B₂≡ = <>-commutes↑↑ (Γ′ , B₁) B₂ (,tys≡ refl p B₁≡)
<>-commutes↑↑ Γ′ (El' B) p 
  = El≡ (refl ++≡ p) (≡[]≡-irrev (<>-commutes↑↑-tm Γ′ B p))

<>-commutes↑↑-sem-sub : ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N} 
                          (p : Γ′ [ ⟨ < N > ⟩s ]tys [ δ ]tys 
                             ≡ Γ′ [ δ ↑m A ]tys [ ⟨ < N [ δ ]tm > ⟩s ]tys)
                      → ⟦ ⟨ < N > ⟩s ↑↑ Γ′ ⟧ms ∘ ⟦ δ ↑↑ Γ′ [ ⟨ < N > ⟩s ]tys ⟧ms
                     ≡[ SemSub≡ ⟦ refl ++≡ p ⟧c≡ refl
                     ]≡ ⟦ (δ ↑m A) ↑↑ Γ′ ⟧ms
                      ∘ ⟦ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ⟧ms
<>-commutes↑↑-sem-sub ε refl = refl
<>-commutes↑↑-sem-sub (Γ′ , B) p 
  = ≡[]≡-irrev (↑sem≡ {A = ⟦ B ⟧T} ⟦ refl ++≡ p′ ⟧c≡ 
                      (<>-commutes↑↑-sem-sub Γ′ p′))
  where p′ = ,proj≡₁ p

<>-commutes↑↑-sem Γ′ B p 
  = []sem≡ B ⟦ refl ++≡ p ⟧c≡ (<>-commutes↑↑-sem-sub Γ′ p) 

-- I would expect both of these rewrites to apply automatically given lam[]
-- is a rewrite rule but for some reason they don't.
lam[]-spec1 : ∀ {N : Tm Γ ⟦ B ⟧T} Γ′ {A C} (M : Tm _ C) 
            → lam (M [ (⟨ <_> {A = B} N ⟩s ↑↑ Γ′) ↑m A ]tm) 
                     [ δ ↑↑ Γ′ [ ⟨ <_> {A = B} N ⟩s ]tys ]tm
            ≡ lam (M [ (⟨ <_> {A = B} N ⟩s ↑↑ Γ′) ↑m A ]tm 
                     [ (δ ↑↑ (Γ′ [ ⟨ <_> {A = B} N ⟩s ]tys)) 
                          ↑m A [ ⟨ <_> {A = B} N ⟩s ↑↑ Γ′ ] ]tm)
lam[]-spec1 Γ′ M
  = lam[] {M = (M [ (⟨ _ ⟩s ↑↑ Γ′) ↑m _ ]tm)} (_ ↑↑ Γ′ [ ⟨ _ ⟩s ]tys)

lam[]-spec2 : ∀ {N : Tm Γ ⟦ B ⟧T} Γ′ {A C} (M : Tm _ C)
            → lam (M [ ((δ ↑m B) ↑↑ Γ′) ↑m A ]tm) 
                     [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m B ]tys ]tm 
            ≡ lam (M [ ((δ ↑m B) ↑↑ Γ′) ↑m A ]tm 
                     [ (⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m B ]tys) 
                                           ↑m A  [ (δ ↑m B) ↑↑ Γ′ ] ]tm) 
lam[]-spec2 Γ′ M
  = lam[] {M = M [ ((_ ↑m _) ↑↑ Γ′) ↑m _ ]tm} 
          (⟨ < _ > ⟩s ↑↑ Γ′ [ _ ↑m _ ]tys)
{-# REWRITE lam[]-spec1 lam[]-spec2 #-}

<>-commutes↑↑-tm Γ′ (var x) p = {!   !}
<>-commutes↑↑-tm Γ′ (app M N) p = {!   !}
<>-commutes↑↑-tm Γ′ (lam {A = A} {B = B} M) p 
  = ≡[]≡-irrev (lam≡ (_ ++≡ p) A≡ B≡ M≡)
  where
    A≡ = <>-commutes↑↑ Γ′ A p 
    B≡ = <>-commutes↑↑-sem (Γ′ , A) B (,tys≡ refl p A≡)
    M≡ = <>-commutes↑↑-tm (Γ′ , A) M (,tys≡ refl p A≡)
            
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
  