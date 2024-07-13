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
open import Coincidences.SubNoConf
open import Coincidences.MSub

module Coincidences.Equations where

wk<>-id-↑↑-sem-sub : ∀ {Γ} {A} (Γ′ : SemTys Γ) {N}
                    → (Γ≡ : Γ′ [ semwk A ]semtys [ sem< N > ]semtys ≡ Γ′)
                    → (semwk A ↑↑sem Γ′) ∘ (sem< N > ↑↑sem Γ′ [ semwk A ]semtys)
                   ≡[ SemSub≡ (refl ++s≡ Γ≡) refl ]≡ id
wk<>-id-↑↑-sem-sub ε refl = refl
wk<>-id-↑↑-sem-sub (Γ′ , A) Γ≡ 
  = ↑s≡ (refl ++s≡ Γ≡′) (wk<>-id-↑↑-sem-sub Γ′ Γ≡′)
  where Γ≡′ = ,proj≡s₁ Γ≡

<>-comm-↑↑s-sem-sub : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} Γ′ {N : _}
                    → (Γ≡ : Γ′ [ sem< N > ]semtys [ δ ]semtys
                          ≡ Γ′ [ δ ↑s A ]semtys [ sem< N ∘ δ > ]semtys)
                    → (sem< N > ↑↑sem Γ′) ∘ (δ ↑↑sem Γ′ [ sem< N > ]semtys)
                   ≡[ SemSub≡ (refl ++s≡ Γ≡) refl
                   ]≡ ((δ ↑s A) ↑↑sem Γ′) 
                        ∘ (sem< N ∘ δ > ↑↑sem Γ′ [ δ ↑s A ]semtys) 
<>-comm-↑↑s-sem-sub ε refl = refl
<>-comm-↑↑s-sem-sub (Γ′ , A) Γ≡ 
  = ↑s≡ (refl ++s≡ Γ≡′) (<>-comm-↑↑s-sem-sub Γ′ Γ≡′)
  where Γ≡′ = ,proj≡s₁ Γ≡
  

wk<>-id-↑↑-sem : ∀ {Γ} {A} (Γ′ : SemTys Γ) {N} B
                → (Γ≡ : Γ′ [ semwk A ]semtys [ sem< N > ]semtys ≡ Γ′)
                → B ∘ (semwk A ↑↑sem Γ′) ∘ (sem< N > ↑↑sem Γ′ [ semwk A ]semtys)
                ≡[ SemTy≡ (refl ++s≡ Γ≡) ]≡ B
wk<>-id-↑↑-sem Γ′ B Γ≡ = []sem≡ (erefl B) (wk<>-id-↑↑-sem-sub Γ′ Γ≡)

<>-comm-↑↑s-sem : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} Γ′ {N : _} B
                → (Γ≡ : Γ′ [ sem< N > ]semtys [ δ ]semtys
                      ≡ Γ′ [ δ ↑s A ]semtys [ sem< N ∘ δ > ]semtys)
                → B ∘ (sem< N > ↑↑sem Γ′) ∘ (δ ↑↑sem Γ′ [ sem< N > ]semtys)
               ≡[ SemTy≡ (refl ++s≡ Γ≡) 
               ]≡ B ∘ ((δ ↑s A) ↑↑sem Γ′) 
                    ∘ (sem< N ∘ δ > ↑↑sem Γ′ [ δ ↑s A ]semtys) 
<>-comm-↑↑s-sem Γ′ B Γ≡ = []sem≡ (erefl B) (<>-comm-↑↑s-sem-sub Γ′ Γ≡)


wk<>-id-↑↑ : ∀ {Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} B
            → (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
            → B [ wk {A = A} ↑↑w Γ′ ]w [ < N > ↑↑s Γ′ [ wk ]wtys ]s
            ≡[ Ty≡ (refl ++≡ Γ≡) ]≡ B

<>-comm-↑↑s : ∀ {δ : Sub Δ Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} B
            → (Γ≡ : Γ′ [ < N > ]stys [ δ ]stys 
                      ≡ Γ′ [ δ ↑ A ]stys [ < N [ δ ]stm > ]stys)
            → B [ < N > ↑↑s Γ′ ]s [ δ ↑↑s Γ′ [ < N > ]stys ]s
           ≡[ Ty≡ (refl ++≡ Γ≡) 
           ]≡ B [ (δ ↑ A) ↑↑s Γ′ ]s [ < N [ δ ]stm > ↑↑s Γ′ [ δ ↑ A ]stys ]s

wk<>-id-↑↑-tm : ∀ {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (M : Tm _ B) 
               → (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
               → M [ wk {A = A} ↑↑w Γ′ ]wtm [ < N > ↑↑s Γ′ [ wk ]wtys ]stm
              ≡[ Tm≡ (refl ++≡ Γ≡)  
                     ( (wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡ ⟧tys≡)) 
              ]≡ M

wk<>-id-↑↑-v : ∀ {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (x : Var _ B) 
                → (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
                → x [ wk {A = A} ↑↑w Γ′ ]wv [ < N > ↑↑s Γ′ [ wk ]wtys ]sv 
               ≡[ Tm≡ (refl ++≡ Γ≡) (wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡ ⟧tys≡)
               ]≡ var x

<>-comm-↑↑s-v : ∀ (δ : Sub Δ Γ) {A} Γ′ {N B} (x : Var _ B) 
              → (Γ≡ : Γ′ [ < N > ]stys [ δ ]stys 
                    ≡ Γ′ [ δ ↑ A ]stys [ < N [ δ ]stm > ]stys)
              → x [ < N > ↑↑s Γ′ ]sv [ δ ↑↑s Γ′ [ < N > ]stys ]stm 
              ≡[ Tm≡ (refl ++≡ Γ≡) (<>-comm-↑↑s-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡ ⟧tys≡)
              ]≡ x [ (δ ↑ A) ↑↑s Γ′ ]sv
                   [ < N [ δ ]stm > ↑↑s Γ′ [ δ ↑ A ]stys ]stm

wk<>-id-↑↑-tm Γ′ (var x) Γ≡ = wk<>-id-↑↑-v Γ′ x Γ≡
wk<>-id-↑↑-tm Γ′ (app {A = A} {B = B} M N) Γ≡ 
  = ≡[]≡-uip (app≡ (refl ++≡ Γ≡) A≡ B≡ (≡[]≡-uip M≡) N≡)
  where A≡ = wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys A ⟦ Γ≡ ⟧tys≡
        B≡ = wk<>-id-↑↑-sem (⟦ Γ′ ⟧tys , A) B 
                            (,semtys≡ refl ⟦ Γ≡ ⟧tys≡ A≡)
        M≡ = wk<>-id-↑↑-tm Γ′ M Γ≡
        N≡ = wk<>-id-↑↑-tm Γ′ N Γ≡
wk<>-id-↑↑-tm Γ′ (lam M) Γ≡ = {!   !}

-- <>-commutes↑↑-tm Γ′ (var x) p = <>-commutes↑↑-v Γ′ x p
-- <>-commutes↑↑-tm Γ′ (app {A = A} {B = B} M N) p 
--   = ≡[]≡-uip (app≡ (refl ++≡ p) (≡[]≡-uip A≡) (≡[]≡-uip B≡) 
--                                   (≡[]≡-uip M≡) (≡[]≡-uip N≡))
--   where
--     A≡ = <>-commutes↑↑-sem ⟦ Γ′ ⟧tys A ⟦ p ⟧tys≡
--     B≡ = <>-commutes↑↑-sem (⟦ Γ′ ⟧tys , A) B 
--                            (,semtys≡ refl ⟦ p ⟧tys≡ (≡[]≡-uip A≡))
--     M≡ = <>-commutes↑↑-tm Γ′ M p
--     N≡ = <>-commutes↑↑-tm Γ′ N p
-- <>-commutes↑↑-tm Γ′ (lam {A = A} {B = B} M) p 
--   = ≡[]≡-uip (lam≡ (_ ++≡ p) A≡ (≡[]≡-uip B≡) (≡[]≡-uip M≡))
--   where
--     A≡ = <>-commutes↑↑ Γ′ A p 
--     B≡ = <>-commutes↑↑-sem ⟦ Γ′ , A ⟧tys B ⟦ ,tys≡ _ p A≡ ⟧tys≡
--     M≡ = <>-commutes↑↑-tm (Γ′ , A) M (,tys≡ refl p A≡)


-- Lemmas over variable substitutions - the actually interesting bit!
wk<>-id-↑↑-v ε x refl = refl
wk<>-id-↑↑-v (Γ′ , A) vz Γ≡ 
  = ≡[]≡-uip (var≡ _ _ (vz≡ _ A≡))
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk<>-id-↑↑ Γ′ A Γ≡′
wk<>-id-↑↑-v (Γ′ , A) (vs {B = B} x) Γ≡ 
  = ≡[]≡-uip ([]wtm≡ {Γ≡ = refl ++≡ Γ≡′} B≡ (wk≡ A≡) (wk<>-id-↑↑-v Γ′ x Γ≡′))
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk<>-id-↑↑ Γ′ A Γ≡′
        B≡ = wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡′ ⟧tys≡

<>-comm-↑↑s-v < N > ε vz refl = refl
<>-comm-↑↑s-v (δ ↑ A) ε vz refl = refl
<>-comm-↑↑s-v _ ε (vs x) refl = sym (wk<>-id-↑↑-tm ε _ refl)
<>-comm-↑↑s-v δ (Γ′ , A) vz Γ≡ 
  = ≡[]≡-uip (var≡ _ _ (vz≡ _ A≡))
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = <>-comm-↑↑s Γ′ A Γ≡′
<>-comm-↑↑s-v δ (Γ′ , A) (vs {B = B} x) Γ≡ = {!ind!}
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = <>-comm-↑↑s Γ′ A Γ≡′   
        B≡ = <>-comm-↑↑s-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡′ ⟧tys≡
        ind = <>-comm-↑↑s-v δ Γ′ x Γ≡′   
