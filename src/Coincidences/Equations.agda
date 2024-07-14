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

module Coincidences.Equations where

-- Proofs on Semantics
wk<>-id-↑↑-sem-sub : ∀ {Γ} {A} (Γ′ : SemTys Γ) {N}
                   → (Γ≡ : Γ′ [ semwk A ]semtys [ sem< N > ]semtys ≡ Γ′)
                   → (semwk A ↑↑sem Γ′) ∘ (sem< N > ↑↑sem Γ′ [ semwk A ]semtys)
                  ≡[ SemSub≡ (refl ++s≡ Γ≡) refl ]≡ id
wk<>-id-↑↑-sem-sub ε refl = refl
wk<>-id-↑↑-sem-sub (Γ′ , A) Γ≡ 
  = ↑s≡ (refl ++s≡ Γ≡′) (wk<>-id-↑↑-sem-sub Γ′ Γ≡′)
  where Γ≡′ = ,proj≡s₁ Γ≡

wk-comm-↑↑-sem-sub : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} (Γ′ : SemTys Γ)
                   → (Γ≡ : Γ′ [ semwk A ]semtys [ δ ↑s A ]semtys 
                         ≡ Γ′ [ δ ]semtys [ semwk (A ∘ δ) ]semtys)
                   → (semwk A ↑↑sem Γ′) ∘ ((δ ↑s A) ↑↑sem Γ′ [ semwk A ]semtys)
                  ≡[ SemSub≡ (refl ++s≡ Γ≡) refl 
                  ]≡ (δ ↑↑sem Γ′) ∘ (semwk (A ∘ δ) ↑↑sem Γ′ [ δ ]semtys)
wk-comm-↑↑-sem-sub ε refl = refl
wk-comm-↑↑-sem-sub (Γ′ , A) Γ≡ 
  = ↑s≡ (refl ++s≡ Γ≡′) (wk-comm-↑↑-sem-sub Γ′ Γ≡′)
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

wk-comm-↑↑-sem : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} (Γ′ : SemTys Γ) B
                → (Γ≡ : Γ′ [ semwk A ]semtys [ δ ↑s A  ]semtys 
                      ≡  Γ′ [ δ ]semtys [ semwk (A ∘ δ) ]semtys)
                → B ∘ (semwk A ↑↑sem Γ′) ∘ ((δ ↑s A) ↑↑sem Γ′ [ semwk A ]semtys)
               ≡[ SemTy≡ (refl ++s≡ Γ≡) 
               ]≡ B ∘ (δ ↑↑sem Γ′) ∘ (semwk (A ∘ δ) ↑↑sem Γ′ [ δ ]semtys)
wk-comm-↑↑-sem Γ′ B Γ≡ = []sem≡ (erefl B) (wk-comm-↑↑-sem-sub Γ′ Γ≡)

<>-comm-↑↑s-sem : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} Γ′ {N : _} B
                → (Γ≡ : Γ′ [ sem< N > ]semtys [ δ ]semtys
                      ≡ Γ′ [ δ ↑s A ]semtys [ sem< N ∘ δ > ]semtys)
                → B ∘ (sem< N > ↑↑sem Γ′) ∘ (δ ↑↑sem Γ′ [ sem< N > ]semtys)
               ≡[ SemTy≡ (refl ++s≡ Γ≡) 
               ]≡ B ∘ ((δ ↑s A) ↑↑sem Γ′) 
                    ∘ (sem< N ∘ δ > ↑↑sem Γ′ [ δ ↑s A ]semtys) 
<>-comm-↑↑s-sem Γ′ B Γ≡ = []sem≡ (erefl B) (<>-comm-↑↑s-sem-sub Γ′ Γ≡)


-- Proofs on Syntax
wk<>-id-↑↑ : ∀ {Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} B
               (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
            → B [ wk {A = A} ↑↑w Γ′ ]w [ < N > ↑↑s Γ′ [ wk ]wtys ]s
            ≡[ Ty≡ (refl ++≡ Γ≡) ]≡ B

wk-comm-↑↑s : ∀ {δ : Sub Δ Γ} {A} Γ′ B
                (Γ≡ : Γ′ [ wk {A = A} ]wtys [ δ ↑ A ]stys 
                    ≡ Γ′ [ δ ]stys [ wk ]wtys)
            → B [ wk {A = A} ↑↑w Γ′ ]w [ (δ ↑ A) ↑↑s Γ′ [ wk ]wtys ]s
           ≡[ Ty≡ (refl ++≡ Γ≡) 
           ]≡ B [ δ ↑↑s Γ′ ]s [ wk ↑↑w Γ′ [ δ ]stys ]w

<>-comm-↑↑s : ∀ {δ : Sub Δ Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} B
                (Γ≡ : Γ′ [ < N > ]stys [ δ ]stys 
                    ≡ Γ′ [ δ ↑ A ]stys [ < N [ δ ]stm > ]stys)
            → B [ < N > ↑↑s Γ′ ]s [ δ ↑↑s Γ′ [ < N > ]stys ]s
           ≡[ Ty≡ (refl ++≡ Γ≡) 
           ]≡ B [ (δ ↑ A) ↑↑s Γ′ ]s [ < N [ δ ]stm > ↑↑s Γ′ [ δ ↑ A ]stys ]s

wk<>-id-↑↑-tm : ∀ {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (M : Tm _ B) 
                  (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
              → M [ wk {A = A} ↑↑w Γ′ ]wtm [ < N > ↑↑s Γ′ [ wk ]wtys ]stm
             ≡[ Tm≡ (refl ++≡ Γ≡) (wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡ ⟧tys≡)
             ]≡ M

wk-comm-↑↑s-tm : ∀ {δ : Sub Δ Γ} {A} Γ′ {B} (M : Tm _ B) 
                  (Γ≡ : Γ′ [ wk {A = A} ]wtys [ δ ↑ A ]stys 
                      ≡ Γ′ [ δ ]stys [ wk ]wtys)
               → M [ wk {A = A} ↑↑w Γ′ ]wtm [ (δ ↑ A) ↑↑s Γ′ [ wk ]wtys ]stm
              ≡[ Tm≡ (refl ++≡ Γ≡) (wk-comm-↑↑-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡ ⟧tys≡)
              ]≡ M [ δ ↑↑s Γ′ ]stm [ wk ↑↑w Γ′ [ δ ]stys ]wtm

<>-comm-↑↑s-tm : ∀ {δ : Sub Δ Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (M : Tm _ B) 
                   (Γ≡ : Γ′ [ < N > ]stys [ δ ]stys 
                      ≡ Γ′ [ δ ↑ A ]stys [ < N [ δ ]stm > ]stys)
               → M [ < N > ↑↑s Γ′ ]stm [ δ ↑↑s Γ′ [ < N > ]stys ]stm
              ≡[ Tm≡ (refl ++≡ Γ≡) (<>-comm-↑↑s-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡ ⟧tys≡)
              ]≡ M [ (δ ↑ A) ↑↑s Γ′ ]stm 
                   [ < N [ δ ]stm > ↑↑s Γ′ [ δ ↑ A ]stys ]stm


wk<>-id-↑↑-v : ∀ {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (x : Var _ B) 
                → (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
                → x [ wk {A = A} ↑↑w Γ′ ]wv [ < N > ↑↑s Γ′ [ wk ]wtys ]sv 
               ≡[ Tm≡ (refl ++≡ Γ≡) (wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡ ⟧tys≡)
               ]≡ var x

wk-comm-↑↑s-v : ∀ {δ : Sub Δ Γ} {A} Γ′ {B} (x : Var _ B) 
                  (Γ≡ : Γ′ [ wk {A = A} ]wtys [ δ ↑ A ]stys 
                      ≡ Γ′ [ δ ]stys [ wk ]wtys)
               → x [ wk {A = A} ↑↑w Γ′ ]wv [ (δ ↑ A) ↑↑s Γ′ [ wk ]wtys ]sv
              ≡[ Tm≡ (refl ++≡ Γ≡) (wk-comm-↑↑-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡ ⟧tys≡)
              ]≡ x [ δ ↑↑s Γ′ ]sv [ wk ↑↑w Γ′ [ δ ]stys ]wtm

<>-comm-↑↑s-v : ∀ (δ : Sub Δ Γ) {A} Γ′ {N B} (x : Var _ B) 
              → (Γ≡ : Γ′ [ < N > ]stys [ δ ]stys 
                    ≡ Γ′ [ δ ↑ A ]stys [ < N [ δ ]stm > ]stys)
              → x [ < N > ↑↑s Γ′ ]sv [ δ ↑↑s Γ′ [ < N > ]stys ]stm 
              ≡[ Tm≡ (refl ++≡ Γ≡) (<>-comm-↑↑s-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡ ⟧tys≡)
              ]≡ x [ (δ ↑ A) ↑↑s Γ′ ]sv
                   [ < N [ δ ]stm > ↑↑s Γ′ [ δ ↑ A ]stys ]stm

wk<>-id-↑↑ Γ′ ⊥' Γ≡ = ⊥≡ _
wk<>-id-↑↑ Γ′ (Π' B₁ B₂) Γ≡ = Π≡ B₁≡ B₂≡
  where B₁≡ = wk<>-id-↑↑ Γ′ B₁ Γ≡
        B₂≡ = wk<>-id-↑↑ (Γ′ , B₁) B₂ (,tys≡ Γ≡ B₁≡)
wk<>-id-↑↑ Γ′ (El' M) Γ≡ = El≡ (≡[]≡-uip (wk<>-id-↑↑-tm Γ′ M Γ≡))

wk<>-id-↑↑-tm Γ′ (var x) Γ≡ = wk<>-id-↑↑-v Γ′ x Γ≡
wk<>-id-↑↑-tm Γ′ (app {A = A} {B = B} M N) Γ≡ 
  = ≡[]≡-uip (app≡ (refl ++≡ Γ≡) A≡ B≡ (≡[]≡-uip M≡) N≡)
  where A≡ = wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys A ⟦ Γ≡ ⟧tys≡
        B≡ = wk<>-id-↑↑-sem (⟦ Γ′ ⟧tys , A) B 
                            (,semtys≡ refl ⟦ Γ≡ ⟧tys≡ A≡)
        M≡ = wk<>-id-↑↑-tm Γ′ M Γ≡
        N≡ = wk<>-id-↑↑-tm Γ′ N Γ≡
wk<>-id-↑↑-tm Γ′ (lam {A = A} {B = B} M) Γ≡ 
  = ≡[]≡-uip (lam≡ A≡ _ M≡)
  where
    A≡ = wk<>-id-↑↑ Γ′ A Γ≡ 
    M≡ = wk<>-id-↑↑-tm (Γ′ , A) M (,tys≡ Γ≡ A≡)

wk-comm-↑↑s-tm Γ′ (var x) Γ≡ = wk-comm-↑↑s-v Γ′ x Γ≡
wk-comm-↑↑s-tm Γ′ (app {A = A} {B = B} M N) Γ≡ 
  = ≡[]≡-uip (app≡ (_ ++≡ Γ≡) A≡ B≡ (≡[]≡-uip M≡) N≡)
  where A≡ = wk-comm-↑↑-sem ⟦ Γ′ ⟧tys A ⟦ Γ≡ ⟧tys≡
        B≡ = wk-comm-↑↑-sem (⟦ Γ′ ⟧tys , A) B 
                            (,semtys≡ refl ⟦ Γ≡ ⟧tys≡ A≡)
        M≡ = wk-comm-↑↑s-tm Γ′ M Γ≡
        N≡ = wk-comm-↑↑s-tm Γ′ N Γ≡
wk-comm-↑↑s-tm Γ′ (lam {A = A} {B = B} M) Γ≡ 
  = ≡[]≡-uip (lam≡ A≡ _ M≡)
  where
    A≡ = wk-comm-↑↑s Γ′ A Γ≡ 
    M≡ = wk-comm-↑↑s-tm (Γ′ , A) M (,tys≡ Γ≡ A≡)

-- Lemmas over variable substitutions - the actually interesting bit!
wk<>-id-↑↑-v ε x refl = refl
wk<>-id-↑↑-v (Γ′ , A) vz Γ≡ 
  = ≡[]≡-uip (var≡ _ _ (vz≡ _ A≡))
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk<>-id-↑↑ Γ′ A Γ≡′
wk<>-id-↑↑-v (Γ′ , A) (vs {B = B} x) Γ≡ 
  = ≡[]≡-uip ([]wtm≡ {Γ≡ = _ ++≡ Γ≡′} _ (wk≡ A≡) (wk<>-id-↑↑-v Γ′ x Γ≡′))
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk<>-id-↑↑ Γ′ A Γ≡′
  
wk-comm-↑↑s-v ε x refl = refl
wk-comm-↑↑s-v (Γ′ , A) vz Γ≡
  = ≡[]≡-uip (var≡ _ _ (vz≡ _ A≡))
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk-comm-↑↑s Γ′ A Γ≡′
wk-comm-↑↑s-v (Γ′ , A) (vs {B = B} x) Γ≡ 
  = ≡[]≡-uip ([]wtm≡ {Γ≡ = _ ++≡ Γ≡′} _ (wk≡ A≡) (wk-comm-↑↑s-v Γ′ x Γ≡′) 
 ∙P {!!})
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk-comm-↑↑s Γ′ A Γ≡′

<>-comm-↑↑s-v < N > ε vz refl = refl
<>-comm-↑↑s-v (δ ↑ A) ε vz refl = refl
<>-comm-↑↑s-v _ ε (vs x) refl = sym (wk<>-id-↑↑-tm ε _ refl)
<>-comm-↑↑s-v δ (Γ′ , A) vz Γ≡ 
  = ≡[]≡-uip (var≡ _ _ (vz≡ _ A≡))
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = <>-comm-↑↑s Γ′ A Γ≡′
<>-comm-↑↑s-v δ (Γ′ , A) (vs {B = B} x) Γ≡ = {![]wtm≡ {Γ≡ = refl ++≡ Γ≡′} B≡ (wk≡ A≡) ind!}
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = <>-comm-↑↑s Γ′ A Γ≡′   
        B≡ = <>-comm-↑↑s-sem ⟦ Γ′ ⟧tys B ⟦ Γ≡′ ⟧tys≡
        ind = <>-comm-↑↑s-v δ Γ′ x Γ≡′   
 