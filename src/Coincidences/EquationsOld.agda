{-# OPTIONS --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; erefl; cong; cong₂; subst; dcong₂; sym)
  renaming (trans to _∙_)
open import Function using (_∘_; case_of_; id)
open import Data.Product using (_,_; proj₁; proj₂)

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Sub
open import Coincidences.MSub

-- This is a proof-of-concept that we can prove lemmas about substitutions
-- can be proven over types, lists of types and terms as long as it can be
-- proven for variables.
--
-- Unfortunately, variables is the actually tricky case. The proof needs to
-- follow the implementation of substitution, but this isn't really possible
-- to do a in a structurally terminating way with MSub. We must instead prove
-- substitution lemmas for single-substitutions (and accept the duplication).
module Coincidences.EquationsOld where

<>-commutes-tys : ∀ {N} Γ′ 
                → Γ′ [ ⟨ < N > ⟩s ]tys [ δ ]tys 
                ≡ Γ′ [ δ ↑m A ]tys [ ⟨ < N [ δ ]tm > ⟩s ]tys
<>-commutes↑↑ : ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N} B 
                  (p : Γ′ [ ⟨ < N > ⟩s ]tys [ δ ]tys 
                     ≡ Γ′ [ δ ↑m A ]tys [ ⟨ < N [ δ ]tm > ⟩s ]tys)
              → B [ ⟨ < N > ⟩s ↑↑ Γ′ ] [ δ ↑↑ Γ′ [ ⟨ < N > ⟩s ]tys ] 
             ≡[ Ty≡ (refl ++≡ p)
             ]≡ B [ (δ ↑m A) ↑↑ Γ′ ] [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]
<>-commutes↑↑-sem : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} Γ′ {N} B 
                      (p : Γ′ [ sem< N > ]semtys [ δ ]semtys 
                         ≡ Γ′ [ δ ↑s A ]semtys [ sem< N ∘ δ > ]semtys)
                  → B ∘ (sem< N > ↑↑sem Γ′) ∘ (δ ↑↑sem Γ′ [ sem< N > ]semtys)
                 ≡[ SemTy≡ (refl ++s≡ p)
                 ]≡ B ∘ ((δ ↑s A) ↑↑sem Γ′) 
                      ∘ (sem< N ∘ δ > ↑↑sem Γ′ [ δ ↑s A ]semtys) 

<>-commutes↑↑-tm :  ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N B} (M : Tm _ B) 
                      (p : Γ′ [ ⟨ < N > ⟩s ]tys [ δ ]tys 
                         ≡ Γ′ [ δ ↑m A ]tys [ ⟨ < N [ δ ]tm > ⟩s ]tys)
                 → M [ ⟨ < N > ⟩s ↑↑ Γ′ ]tm [ δ ↑↑ Γ′ [ ⟨ < N > ⟩s ]tys ]tm 
                ≡[ Tm≡ (refl ++≡ p) 
                       (≡[]≡-uip (<>-commutes↑↑-sem ⟦ Γ′ ⟧tys B ⟦ p ⟧tys≡))
                ]≡ M [ (δ ↑m A) ↑↑ Γ′ ]tm
                     [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]tm

<>-commutes↑↑-v : ∀ {Γ Δ} {δ : MSub Δ Γ} {A} Γ′ {N B} (M : Var _ B) 
                    (p : Γ′ [ ⟨ < N > ⟩s ]tys [ δ ]tys 
                       ≡ Γ′ [ δ ↑m A ]tys [ ⟨ < N [ δ ]tm > ⟩s ]tys)
                → M [ ⟨ < N > ⟩s ↑↑ Γ′ ]v [ δ ↑↑ Γ′ [ ⟨ < N > ⟩s ]tys ]tm 
               ≡[ Tm≡ (refl ++≡ p) 
                      (≡[]≡-uip (<>-commutes↑↑-sem ⟦ Γ′ ⟧tys B ⟦ p ⟧tys≡))
               ]≡ M [ (δ ↑m A) ↑↑ Γ′ ]v 
                    [ ⟨ < N [ δ ]tm > ⟩s ↑↑ Γ′ [ δ ↑m A ]tys ]tm

<>-commutes-tys ε = refl
<>-commutes-tys (Γ′ , B) = ,tys≡ Γ≡′ (<>-commutes↑↑ Γ′ B Γ≡′)
  where Γ≡′ = <>-commutes-tys Γ′

<>-commutes↑↑ Γ′ ⊥' p = ⊥≡ (refl ++≡ p)
<>-commutes↑↑ Γ′ (Π' B₁ B₂) p 
  = Π≡ B₁≡ (≡[]≡-uip B₂≡)
  where B₁≡ = <>-commutes↑↑ Γ′ B₁ p
        B₂≡ = <>-commutes↑↑ (Γ′ , B₁) B₂ (,tys≡ p B₁≡)
<>-commutes↑↑ Γ′ (El' B) p 
  = El≡ (≡[]≡-uip (<>-commutes↑↑-tm Γ′ B p))

<>-commutes↑↑-sem-sub : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} Γ′ {N} 
                          (p : Γ′ [ sem< N > ]semtys [ δ ]semtys 
                             ≡ Γ′ [ δ ↑s A ]semtys [ sem< N ∘ δ > ]semtys)
                       → (sem< N > ↑↑sem Γ′) ∘ (δ ↑↑sem Γ′ [ sem< N > ]semtys)
                      ≡[ SemSub≡ (refl ++s≡ p) refl
                      ]≡ ((δ ↑s A) ↑↑sem Γ′)
                       ∘ (sem< N ∘ δ > ↑↑sem Γ′ [ δ ↑s A ]semtys)
<>-commutes↑↑-sem-sub ε refl = refl
<>-commutes↑↑-sem-sub (Γ′ , B) p 
  = ≡[]≡-uip (↑s≡ (refl ++s≡ p′) (<>-commutes↑↑-sem-sub Γ′ p′))
  where p′ = ,proj≡s₁ p

<>-commutes↑↑-sem Γ′ B p 
  = []sem≡ (erefl B) (<>-commutes↑↑-sem-sub Γ′ p) 

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

<>-commutes↑↑-v {δ = idₛ} ε vz refl = drefl _
<>-commutes↑↑-v {δ = δ ◂w σ} ε {N = N} (vz {A = A}) refl = bar ∙ baz
  where foo = <>-commutes↑↑-v {δ = δ} ε {N = N} vz refl
        bar = cong _[ σ ]wtm foo
        baz = <>-commutes↑↑-tm {δ = {!idₛ ◂w σ!}} ε (vz [ δ ↑m A ]v) refl
<>-commutes↑↑-v {δ = δ ◂s σ} ε vz refl = {!   !}
<>-commutes↑↑-v {δ = idₛ} ε (vs x) p = drefl _
<>-commutes↑↑-v {δ = δ ◂w σ} ε (vs x) p = {!   !}
<>-commutes↑↑-v {δ = δ ◂s σ} ε (vs x) p = {!   !}
<>-commutes↑↑-v (Γ′ , C) x p = {!   !}

<>-commutes↑↑-tm Γ′ (var x) p = <>-commutes↑↑-v Γ′ x p
<>-commutes↑↑-tm Γ′ (app {A = A} {B = B} M N) p 
  = ≡[]≡-uip (app≡ (refl ++≡ p) (≡[]≡-uip A≡) (≡[]≡-uip B≡) 
                                  (≡[]≡-uip M≡) (≡[]≡-uip N≡))
  where
    A≡ = <>-commutes↑↑-sem ⟦ Γ′ ⟧tys A ⟦ p ⟧tys≡
    B≡ = <>-commutes↑↑-sem (⟦ Γ′ ⟧tys , A) B 
                           (,semtys≡ refl ⟦ p ⟧tys≡ (≡[]≡-uip A≡))
    M≡ = <>-commutes↑↑-tm Γ′ M p
    N≡ = <>-commutes↑↑-tm Γ′ N p
<>-commutes↑↑-tm Γ′ (lam {A = A} {B = B} M) p 
  = ≡[]≡-uip (lam≡ A≡ (≡[]≡-uip B≡) (≡[]≡-uip M≡))
  where
    A≡ = <>-commutes↑↑ Γ′ A p 
    B≡ = <>-commutes↑↑-sem ⟦ Γ′ , A ⟧tys B ⟦ ,tys≡ p A≡ ⟧tys≡
    M≡ = <>-commutes↑↑-tm (Γ′ , A) M (,tys≡ p A≡)
            
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
    