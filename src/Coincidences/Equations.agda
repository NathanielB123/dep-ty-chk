{-# OPTIONS --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; subst; dcong₂; sym; erefl)
  renaming (trans to _∙_)
open import Function using (_∘_; case_of_; id)
open import Data.Product using (_,_; proj₁; proj₂)

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Sub

module Coincidences.Equations where

wk<>-id-↑↑s : ∀ {Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} B
            → (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
            → B [ wk {A = A} ↑↑w Γ′ ]w [ < N > ↑↑s Γ′ [ wk ]wtys ]s
            ≡[ Ty≡ (refl ++≡ Γ≡) ]≡ B

wk<>-id-↑↑s-sem-sub : ∀ {Γ} {A} (Γ′ : SemTys Γ) {N : _}
                    → (Γ≡ : Γ′ [ semwk A ]semtys [ sem< N > ]semtys ≡ Γ′)
                    → (semwk A ↑↑sem Γ′) ∘ (sem< N > ↑↑sem Γ′ [ semwk A ]semtys)
                   ≡[ SemSub≡ (refl ++s≡ Γ≡) refl ]≡ id
wk<>-id-↑↑s-sem-sub ε refl = refl
wk<>-id-↑↑s-sem-sub (Γ′ , A) Γ≡ 
  = ≡[]≡-uip (↑s≡ (refl ++s≡ Γ≡′) (wk<>-id-↑↑s-sem-sub Γ′ Γ≡′))
  where Γ≡′ = ,proj≡s₁ Γ≡

wk<>-id-↑↑s-sem : ∀ {Γ} {A} (Γ′ : SemTys Γ) {N : _} B
                → (Γ≡ : Γ′ [ semwk A ]semtys [ sem< N > ]semtys ≡ Γ′)
                → B ∘ (semwk A ↑↑sem Γ′) ∘ (sem< N > ↑↑sem Γ′ [ semwk A ]semtys)
                ≡[ SemTy≡ (refl ++s≡ Γ≡) ]≡ B
wk<>-id-↑↑s-sem Γ′ B Γ≡ = []sem≡ (erefl B) (wk<>-id-↑↑s-sem-sub Γ′ Γ≡)

wk<>-id-↑↑s-v : ∀ {Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (x : Var _ B) 
                → (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
                → x [ wk {A = A} ↑↑w Γ′ ]wv [ < N > ↑↑s Γ′ [ wk ]wtys ]sv 
               ≡[ Tm≡ (refl ++≡ Γ≡) 
                      (≡[]≡-uip (wk<>-id-↑↑s-sem ⟦ Γ′ ⟧tys B (⟦⟧tys≡ _ Γ≡))) 
               ]≡ var x
wk<>-id-↑↑s-v ε x refl = refl
wk<>-id-↑↑s-v (Γ′ , A) vz Γ≡ 
  = ≡[]≡-uip (var≡ (refl ++≡ Γ≡) (≡[]≡-uip (semwk≡ _ Asem≡ Asem≡)) 
             (≡[]≡-uip (vz≡ _ Asyn≡)))
  where Γ≡′ = ,proj≡₁ Γ≡
        Asyn≡ = wk<>-id-↑↑s Γ′ A Γ≡′
        Asem≡ = ⟦⟧T≡ (refl ++≡ Γ≡′) Asyn≡
wk<>-id-↑↑s-v (Γ′ , A) (vs {B = B} x) Γ≡ 
  = ≡[]≡-uip ([]wtm≡ (≡[]≡-uip B≡) (wk≡ A≡) (wk<>-id-↑↑s-v Γ′ x Γ≡′))
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk<>-id-↑↑s Γ′ A Γ≡′
        B≡ = wk<>-id-↑↑s-sem ⟦ Γ′ ⟧tys B (⟦⟧tys≡ _ Γ≡′)

<>-commutes-↑↑s-v :  ∀ {Γ Δ} (δ : Sub Δ Γ) {A} Γ′ {N B} (x : Var _ B) 
                → (Γ≡ : Γ′ [ < N > ]stys [ δ ]stys 
                      ≡ Γ′ [ δ ↑ A ]stys [ < N [ δ ]stm > ]stys)
                → x [ < N > ↑↑s Γ′ ]sv [ δ ↑↑s Γ′ [ < N > ]stys ]stm 
                ≡[ Tm≡ (refl ++≡ Γ≡) {!!} 
                ]≡ x [ (δ ↑ A) ↑↑s Γ′ ]sv
                     [ < N [ δ ]stm > ↑↑s Γ′ [ δ ↑ A ]stys ]stm
<>-commutes-↑↑s-v < N > ε vz refl = {!   !}
<>-commutes-↑↑s-v (δ ↑ A) ε vz refl = {!   !}
<>-commutes-↑↑s-v < N > ε (vs x) refl = {!   !}
<>-commutes-↑↑s-v (δ ↑ A) ε (vs x) refl = {!   !} 
<>-commutes-↑↑s-v δ (Γ′ , _) x Γ≡ = {!   !} 