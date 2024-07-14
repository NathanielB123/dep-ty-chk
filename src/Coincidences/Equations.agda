{-# OPTIONS --rewriting --prop --show-irrelevant #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Sub
open import Coincidences.SubNoConf

-- This file is basically the same proof over and over again
-- Sadly, we can't easily abstract over the substitution lemma without Agda 
-- complaining about termination
module Coincidences.Equations where

-- Lemmas we shall prove:
-- M [ wk     ] [ < N >  ] ≡ M                        (wk-<>-id)
-- M [ wk ↑ B ] [ < vz > ] ≡ M                        (wk-vz-id)
-- M [ wk     ] [ δ ↑ B       ] ≡ M [ δ     ] [ wk ]  (wk-comm)
-- M [ δ ↑ B  ] [ < N [ δ ] > ] ≡ M [ < N > ] [ δ  ]  (<>-comm)

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

<>-comm-↑↑-sem-sub : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} Γ′ {N : _}
                    → (Γ≡ : Γ′ [ sem< N > ]semtys [ δ ]semtys
                          ≡ Γ′ [ δ ↑s A ]semtys [ sem< N ∘ δ > ]semtys)
                    → (sem< N > ↑↑sem Γ′) ∘ (δ ↑↑sem Γ′ [ sem< N > ]semtys)
                   ≡[ SemSub≡ (refl ++s≡ Γ≡) refl
                   ]≡ ((δ ↑s A) ↑↑sem Γ′) 
                    ∘ (sem< N ∘ δ > ↑↑sem Γ′ [ δ ↑s A ]semtys) 
<>-comm-↑↑-sem-sub ε refl = refl
<>-comm-↑↑-sem-sub (Γ′ , A) Γ≡ 
  = ↑s≡ (refl ++s≡ Γ≡′) (<>-comm-↑↑-sem-sub Γ′ Γ≡′)
  where Γ≡′ = ,proj≡s₁ Γ≡
  

wk<>-id-↑↑-sem : ∀ {Γ} {A} (Γ′ : SemTys Γ) {N} B
                → (Γ≡ : Γ′ [ semwk A ]semtys [ sem< N > ]semtys ≡ Γ′)
                → B ∘ (semwk A ↑↑sem Γ′) ∘ (sem< N > ↑↑sem Γ′ [ semwk A ]semtys)
                ≡[ SemTy≡ (refl ++s≡ Γ≡) ]≡ B
wk<>-id-↑↑-sem Γ′ B Γ≡ 
  = []sem≡ (refl ++s≡ Γ≡) refl (erefl B) (wk<>-id-↑↑-sem-sub Γ′ Γ≡)

wk-comm-↑↑-sem : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} (Γ′ : SemTys Γ) B
                → (Γ≡ : Γ′ [ semwk A ]semtys [ δ ↑s A  ]semtys 
                      ≡  Γ′ [ δ ]semtys [ semwk (A ∘ δ) ]semtys)
                → B ∘ (semwk A ↑↑sem Γ′) ∘ ((δ ↑s A) ↑↑sem Γ′ [ semwk A ]semtys)
               ≡[ SemTy≡ (refl ++s≡ Γ≡) 
               ]≡ B ∘ (δ ↑↑sem Γ′) ∘ (semwk (A ∘ δ) ↑↑sem Γ′ [ δ ]semtys)
wk-comm-↑↑-sem Γ′ B Γ≡ 
  = []sem≡ (refl ++s≡ Γ≡) refl (erefl B) (wk-comm-↑↑-sem-sub Γ′ Γ≡)

<>-comm-↑↑-sem : ∀ {Γ Δ} {δ : SemSub Δ Γ} {A} Γ′ {N : _} B
                → (Γ≡ : Γ′ [ sem< N > ]semtys [ δ ]semtys
                      ≡ Γ′ [ δ ↑s A ]semtys [ sem< N ∘ δ > ]semtys)
                → B ∘ (sem< N > ↑↑sem Γ′) ∘ (δ ↑↑sem Γ′ [ sem< N > ]semtys)
               ≡[ SemTy≡ (refl ++s≡ Γ≡) 
               ]≡ B ∘ ((δ ↑s A) ↑↑sem Γ′) 
                    ∘ (sem< N ∘ δ > ↑↑sem Γ′ [ δ ↑s A ]semtys) 
<>-comm-↑↑-sem Γ′ B Γ≡ 
  = []sem≡ (refl ++s≡ Γ≡) refl (erefl B) (<>-comm-↑↑-sem-sub Γ′ Γ≡)


-- Proofs on Syntax
wk<>-id-↑↑ : ∀ {Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} B
               (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
            → B [ wk {A = A} ↑↑w Γ′ ]w [ < N > ↑↑s Γ′ [ wk ]wtys ]s
            ≡[ Ty≡ (refl ++≡ Γ≡) ]≡ B

wk-comm-↑↑w : ∀ {δ : Wk Δ Γ} {A} Γ′ B
                (Γ≡ : Γ′ [ wk {A = A} ]wtys [ δ ↑ A ]wtys 
                    ≡ Γ′ [ δ ]wtys [ wk ]wtys)
            → B [ wk {A = A} ↑↑w Γ′ ]w [ (δ ↑ A) ↑↑w Γ′ [ wk ]wtys ]w
           ≡[ Ty≡ (refl ++≡ Γ≡) 
           ]≡ B [ δ ↑↑w Γ′ ]w [ wk ↑↑w Γ′ [ δ ]wtys ]w

wk-comm-↑↑s : ∀ {δ : Sub Δ Γ} {A} Γ′ B
                (Γ≡ : Γ′ [ wk {A = A} ]wtys [ δ ↑ A ]stys 
                    ≡ Γ′ [ δ ]stys [ wk ]wtys)
            → B [ wk {A = A} ↑↑w Γ′ ]w [ (δ ↑ A) ↑↑s Γ′ [ wk ]wtys ]s
           ≡[ Ty≡ (refl ++≡ Γ≡) 
           ]≡ B [ δ ↑↑s Γ′ ]s [ wk ↑↑w Γ′ [ δ ]stys ]w

<>-comm-↑↑w : ∀ {δ : Wk Δ Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} B
                (Γ≡ : Γ′ [ < N > ]stys [ δ ]wtys 
                    ≡ Γ′ [ δ ↑ A ]wtys [ < N [ δ ]wtm > ]stys)
            → B [ < N > ↑↑s Γ′ ]s [ δ ↑↑w Γ′ [ < N > ]stys ]w
           ≡[ Ty≡ (refl ++≡ Γ≡) 
           ]≡ B [ (δ ↑ A) ↑↑w Γ′ ]w [ < N [ δ ]wtm > ↑↑s Γ′ [ δ ↑ A ]wtys ]s

<>-comm-↑↑s : ∀ {δ : Sub Δ Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} B
                (Γ≡ : Γ′ [ < N > ]stys [ δ ]stys 
                    ≡ Γ′ [ δ ↑ A ]stys [ < N [ δ ]stm > ]stys)
            → B [ < N > ↑↑s Γ′ ]s [ δ ↑↑s Γ′ [ < N > ]stys ]s
           ≡[ Ty≡ (refl ++≡ Γ≡) 
           ]≡ B [ (δ ↑ A) ↑↑s Γ′ ]s [ < N [ δ ]stm > ↑↑s Γ′ [ δ ↑ A ]stys ]s

wk<>-id-↑↑-tm : ∀ {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (M : Tm _ B) 
                  (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
              → M [ wk {A = A} ↑↑w Γ′ ]wtm [ < N > ↑↑s Γ′ [ wk ]wtys ]stm
             ≡[ Tm≡ (refl ++≡ Γ≡) 
                    (wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
             ]≡ M

wk-comm-↑↑w-tm : ∀ {δ : Wk Δ Γ} {A} Γ′ {B} (M : Tm _ B) 
                  (Γ≡ : Γ′ [ wk {A = A} ]wtys [ δ ↑ A ]wtys 
                      ≡ Γ′ [ δ ]wtys [ wk ]wtys)
               → M [ wk {A = A} ↑↑w Γ′ ]wtm [ (δ ↑ A) ↑↑w Γ′ [ wk ]wtys ]wtm
              ≡[ Tm≡ (refl ++≡ Γ≡) 
                     (wk-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
              ]≡ M [ δ ↑↑w Γ′ ]wtm [ wk ↑↑w Γ′ [ δ ]wtys ]wtm

wk-comm-↑↑s-tm : ∀ {δ : Sub Δ Γ} {A} Γ′ {B} (M : Tm _ B) 
                  (Γ≡ : Γ′ [ wk {A = A} ]wtys [ δ ↑ A ]stys 
                      ≡ Γ′ [ δ ]stys [ wk ]wtys)
               → M [ wk {A = A} ↑↑w Γ′ ]wtm [ (δ ↑ A) ↑↑s Γ′ [ wk ]wtys ]stm
              ≡[ Tm≡ (refl ++≡ Γ≡) 
                     (wk-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
              ]≡ M [ δ ↑↑s Γ′ ]stm [ wk ↑↑w Γ′ [ δ ]stys ]wtm

<>-comm-↑↑w-tm : ∀ {δ : Wk Δ Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (M : Tm _ B) 
                   (Γ≡ : Γ′ [ < N > ]stys [ δ ]wtys 
                      ≡ Γ′ [ δ ↑ A ]wtys [ < N [ δ ]wtm > ]stys)
               → M [ < N > ↑↑s Γ′ ]stm [ δ ↑↑w Γ′ [ < N > ]stys ]wtm
              ≡[ Tm≡ (refl ++≡ Γ≡) 
                     (<>-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
              ]≡ M [ (δ ↑ A) ↑↑w Γ′ ]wtm 
                   [ < N [ δ ]wtm > ↑↑s Γ′ [ δ ↑ A ]wtys ]stm

<>-comm-↑↑s-tm : ∀ {δ : Sub Δ Γ} {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (M : Tm _ B) 
                   (Γ≡ : Γ′ [ < N > ]stys [ δ ]stys 
                      ≡ Γ′ [ δ ↑ A ]stys [ < N [ δ ]stm > ]stys)
               → M [ < N > ↑↑s Γ′ ]stm [ δ ↑↑s Γ′ [ < N > ]stys ]stm
              ≡[ Tm≡ (refl ++≡ Γ≡) 
                     (<>-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
              ]≡ M [ (δ ↑ A) ↑↑s Γ′ ]stm 
                   [ < N [ δ ]stm > ↑↑s Γ′ [ δ ↑ A ]stys ]stm


wk<>-id-↑↑-v : ∀ {A} Γ′ {N : Tm Γ ⟦ A ⟧T} {B} (x : Var _ B) 
                → (Γ≡ : Γ′ [ wk {A = A} ]wtys [ < N > ]stys ≡ Γ′)
                → x [ wk {A = A} ↑↑w Γ′ ]wv [ < N > ↑↑s Γ′ [ wk ]wtys ]sv 
               ≡[ Tm≡ (refl ++≡ Γ≡) 
                      (wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
               ]≡ var x

wk-comm-↑↑w-v : ∀ {δ : Wk Δ Γ} {A} Γ′ {B} (x : Var _ B) 
                  (Γ≡ : Γ′ [ wk {A = A} ]wtys [ δ ↑ A ]wtys 
                      ≡ Γ′ [ δ ]wtys [ wk ]wtys)
               → x [ wk {A = A} ↑↑w Γ′ ]wv [ (δ ↑ A) ↑↑w Γ′ [ wk ]wtys ]wv
              ≡[ Var≡ (refl ++≡ Γ≡) 
                      (wk-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
              ]≡ x [ δ ↑↑w Γ′ ]wv [ wk ↑↑w Γ′ [ δ ]wtys ]wv

wk-comm-↑↑s-v : ∀ {δ : Sub Δ Γ} {A} Γ′ {B} (x : Var _ B) 
                  (Γ≡ : Γ′ [ wk {A = A} ]wtys [ δ ↑ A ]stys 
                      ≡ Γ′ [ δ ]stys [ wk ]wtys)
               → x [ wk {A = A} ↑↑w Γ′ ]wv [ (δ ↑ A) ↑↑s Γ′ [ wk ]wtys ]sv
              ≡[ Tm≡ (refl ++≡ Γ≡) 
                     (wk-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
              ]≡ x [ δ ↑↑s Γ′ ]sv [ wk ↑↑w Γ′ [ δ ]stys ]wtm

<>-comm-↑↑w-v : ∀ {δ : Wk Δ Γ} {A} Γ′ {N B} (x : Var _ B) 
              → (Γ≡ : Γ′ [ < N > ]stys [ δ ]wtys 
                    ≡ Γ′ [ δ ↑ A ]wtys [ < N [ δ ]wtm > ]stys)
              → x [ < N > ↑↑s Γ′ ]sv [ δ ↑↑w Γ′ [ < N > ]stys ]wtm 
              ≡[ Tm≡ (refl ++≡ Γ≡) 
                     (<>-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
              ]≡ x [ (δ ↑ A) ↑↑w Γ′ ]wv
                   [ < N [ δ ]wtm > ↑↑s Γ′ [ δ ↑ A ]wtys ]sv

<>-comm-↑↑s-v : ∀ {δ : Sub Δ Γ} {A} Γ′ {N B} (x : Var _ B) 
              → (Γ≡ : Γ′ [ < N > ]stys [ δ ]stys 
                    ≡ Γ′ [ δ ↑ A ]stys [ < N [ δ ]stm > ]stys)
              → x [ < N > ↑↑s Γ′ ]sv [ δ ↑↑s Γ′ [ < N > ]stys ]stm 
              ≡[ Tm≡ (refl ++≡ Γ≡) 
                     (<>-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡ ]p)
              ]≡ x [ (δ ↑ A) ↑↑s Γ′ ]sv
                   [ < N [ δ ]stm > ↑↑s Γ′ [ δ ↑ A ]stys ]stm

wk<>-id-↑↑ Γ′ ⊥' Γ≡ = ⊥≡ (refl ++≡ Γ≡)
wk<>-id-↑↑ Γ′ (Π' B₁ B₂) Γ≡ = Π≡ (refl ++≡ Γ≡) B₁≡ B₂≡
  where B₁≡ = wk<>-id-↑↑ Γ′ B₁ Γ≡
        B₂≡ = wk<>-id-↑↑ (Γ′ , B₁) B₂ (,tys≡ refl Γ≡ B₁≡)
wk<>-id-↑↑ Γ′ (El' M) Γ≡ = El≡ (refl ++≡ Γ≡) (wk<>-id-↑↑-tm Γ′ M Γ≡)

wk-comm-↑↑w Γ′ ⊥' Γ≡ = ⊥≡ (refl ++≡ Γ≡)
wk-comm-↑↑w Γ′ (Π' B₁ B₂) Γ≡ = Π≡ (refl ++≡ Γ≡) B₁≡ B₂≡
  where B₁≡ = wk-comm-↑↑w Γ′ B₁ Γ≡
        B₂≡ = wk-comm-↑↑w (Γ′ , B₁) B₂ (,tys≡ refl Γ≡ B₁≡)
wk-comm-↑↑w Γ′ (El' M) Γ≡ = El≡ (refl ++≡ Γ≡) (wk-comm-↑↑w-tm Γ′ M Γ≡)

wk-comm-↑↑s Γ′ ⊥' Γ≡ = ⊥≡ (refl ++≡ Γ≡)
wk-comm-↑↑s Γ′ (Π' B₁ B₂) Γ≡ = Π≡ (refl ++≡ Γ≡) B₁≡ B₂≡
  where B₁≡ = wk-comm-↑↑s Γ′ B₁ Γ≡
        B₂≡ = wk-comm-↑↑s (Γ′ , B₁) B₂ (,tys≡ refl Γ≡ B₁≡)
wk-comm-↑↑s Γ′ (El' M) Γ≡ = El≡ (refl ++≡ Γ≡) (wk-comm-↑↑s-tm Γ′ M Γ≡)

<>-comm-↑↑w Γ′ ⊥' Γ≡ = ⊥≡ (refl ++≡ Γ≡)
<>-comm-↑↑w Γ′ (Π' B₁ B₂) Γ≡ = Π≡ (refl ++≡ Γ≡) B₁≡ B₂≡
  where B₁≡ = <>-comm-↑↑w Γ′ B₁ Γ≡
        B₂≡ = <>-comm-↑↑w (Γ′ , B₁) B₂ (,tys≡ refl Γ≡ B₁≡)
<>-comm-↑↑w Γ′ (El' M) Γ≡ = El≡ (refl ++≡ Γ≡) (<>-comm-↑↑w-tm Γ′ M Γ≡)

<>-comm-↑↑s Γ′ ⊥' Γ≡ = ⊥≡ (refl ++≡ Γ≡)
<>-comm-↑↑s Γ′ (Π' B₁ B₂) Γ≡ = Π≡ (refl ++≡ Γ≡) B₁≡ B₂≡
  where B₁≡ = <>-comm-↑↑s Γ′ B₁ Γ≡
        B₂≡ = <>-comm-↑↑s (Γ′ , B₁) B₂ (,tys≡ refl Γ≡ B₁≡)
<>-comm-↑↑s Γ′ (El' M) Γ≡ = El≡ (refl ++≡ Γ≡) (<>-comm-↑↑s-tm Γ′ M Γ≡)

wk<>-id-↑↑-tm Γ′ (var x) Γ≡ = wk<>-id-↑↑-v Γ′ x Γ≡
wk<>-id-↑↑-tm Γ′ (app {A = A} {B = B} M N) Γ≡ 
  = app≡ (refl ++≡ Γ≡) A≡ B≡ M≡ N≡
  where A≡ = wk<>-id-↑↑-sem _ A [ ⟦⟧tys≡ refl Γ≡ ]p
        B≡ = wk<>-id-↑↑-sem _ B (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p A≡)
        M≡ = wk<>-id-↑↑-tm Γ′ M Γ≡
        N≡ = wk<>-id-↑↑-tm Γ′ N Γ≡
wk<>-id-↑↑-tm Γ′ (lam {A = A} {B = B} M) Γ≡ 
  = lam≡ (refl ++≡ Γ≡) A≡ B≡ M≡
  where
    A≡ = wk<>-id-↑↑ Γ′ A Γ≡ 
    B≡ = wk<>-id-↑↑-sem (⟦ Γ′ , A ⟧tys) B 
         (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p (⟦⟧T≡ (refl ++≡ Γ≡) A≡))
    M≡ = wk<>-id-↑↑-tm (Γ′ , A) M (,tys≡ refl Γ≡ A≡)

wk-comm-↑↑w-tm Γ′ (var {A = A} x) Γ≡ 
  = var≡ (refl ++≡ Γ≡) A≡ (wk-comm-↑↑w-v Γ′ x Γ≡)
  where A≡ = wk-comm-↑↑-sem _ A [ ⟦⟧tys≡ refl Γ≡ ]p
wk-comm-↑↑w-tm Γ′ (app {A = A} {B = B} M N) Γ≡ 
  = app≡ (refl ++≡ Γ≡) A≡ B≡ M≡ N≡
  where A≡ = wk-comm-↑↑-sem _ A [ ⟦⟧tys≡ refl Γ≡ ]p
        B≡ = wk-comm-↑↑-sem _ B (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p A≡)
        M≡ = wk-comm-↑↑w-tm Γ′ M Γ≡
        N≡ = wk-comm-↑↑w-tm Γ′ N Γ≡
wk-comm-↑↑w-tm Γ′ (lam {A = A} {B = B} M) Γ≡ 
  = lam≡ (refl ++≡ Γ≡) A≡ B≡ M≡
  where
    A≡ = wk-comm-↑↑w Γ′ A Γ≡ 
    B≡ = wk-comm-↑↑-sem (⟦ Γ′ , A ⟧tys) B 
         (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p (⟦⟧T≡ (refl ++≡ Γ≡) A≡))
    M≡ = wk-comm-↑↑w-tm (Γ′ , A) M (,tys≡ refl Γ≡ A≡)

wk-comm-↑↑s-tm Γ′ (var {A = A} x) Γ≡ = wk-comm-↑↑s-v Γ′ x Γ≡
  where A≡ = wk-comm-↑↑-sem _ A [ ⟦⟧tys≡ refl Γ≡ ]p
wk-comm-↑↑s-tm Γ′ (app {A = A} {B = B} M N) Γ≡ 
  = app≡ (refl ++≡ Γ≡) A≡ B≡ M≡ N≡
  where A≡ = wk-comm-↑↑-sem _ A [ ⟦⟧tys≡ refl Γ≡ ]p
        B≡ = wk-comm-↑↑-sem _ B (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p A≡)
        M≡ = wk-comm-↑↑s-tm Γ′ M Γ≡
        N≡ = wk-comm-↑↑s-tm Γ′ N Γ≡
wk-comm-↑↑s-tm Γ′ (lam {A = A} {B = B} M) Γ≡ 
  = lam≡ (refl ++≡ Γ≡) A≡ B≡ M≡
  where
    A≡ = wk-comm-↑↑s Γ′ A Γ≡ 
    B≡ = wk-comm-↑↑-sem (⟦ Γ′ , A ⟧tys) B 
         (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p (⟦⟧T≡ (refl ++≡ Γ≡) A≡))
    M≡ = wk-comm-↑↑s-tm (Γ′ , A) M (,tys≡ refl Γ≡ A≡)

<>-comm-↑↑w-tm Γ′ (var {A = A} x) Γ≡ = <>-comm-↑↑w-v Γ′ x Γ≡
  where A≡ = <>-comm-↑↑-sem _ A [ ⟦⟧tys≡ refl Γ≡ ]p
<>-comm-↑↑w-tm Γ′ (app {A = A} {B = B} M N) Γ≡ 
  = app≡ (refl ++≡ Γ≡) A≡ B≡ M≡ N≡
  where A≡ = <>-comm-↑↑-sem _ A [ ⟦⟧tys≡ refl Γ≡ ]p
        B≡ = <>-comm-↑↑-sem _ B (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p A≡)
        M≡ = <>-comm-↑↑w-tm Γ′ M Γ≡
        N≡ = <>-comm-↑↑w-tm Γ′ N Γ≡
<>-comm-↑↑w-tm Γ′ (lam {A = A} {B = B} M) Γ≡ 
  = lam≡ (refl ++≡ Γ≡) A≡ B≡ M≡
  where
    A≡ = <>-comm-↑↑w Γ′ A Γ≡ 
    B≡ = <>-comm-↑↑-sem (⟦ Γ′ , A ⟧tys) B 
         (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p (⟦⟧T≡ (refl ++≡ Γ≡) A≡))
    M≡ = <>-comm-↑↑w-tm (Γ′ , A) M (,tys≡ refl Γ≡ A≡)

<>-comm-↑↑s-tm Γ′ (var {A = A} x) Γ≡ = <>-comm-↑↑s-v Γ′ x Γ≡
  where A≡ = <>-comm-↑↑-sem _ A [ ⟦⟧tys≡ refl Γ≡ ]p
<>-comm-↑↑s-tm Γ′ (app {A = A} {B = B} M N) Γ≡ 
  = app≡ (refl ++≡ Γ≡) A≡ B≡ M≡ N≡
  where A≡ = <>-comm-↑↑-sem _ A [ ⟦⟧tys≡ refl Γ≡ ]p
        B≡ = <>-comm-↑↑-sem _ B (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p A≡)
        M≡ = <>-comm-↑↑s-tm Γ′ M Γ≡
        N≡ = <>-comm-↑↑s-tm Γ′ N Γ≡
<>-comm-↑↑s-tm Γ′ (lam {A = A} {B = B} M) Γ≡ 
  = lam≡ (refl ++≡ Γ≡) A≡ B≡ M≡
  where
    A≡ = <>-comm-↑↑s Γ′ A Γ≡ 
    B≡ = <>-comm-↑↑-sem (⟦ Γ′ , A ⟧tys) B 
         (,semtys≡ refl [ ⟦⟧tys≡ refl Γ≡ ]p (⟦⟧T≡ (refl ++≡ Γ≡) A≡))
    M≡ = <>-comm-↑↑s-tm (Γ′ , A) M (,tys≡ refl Γ≡ A≡)

-- -- -- Lemmas over variable substitutions - the actually interesting bit!
-- -- -- Commented out because they make the file take too long to typecheck lol
wk<>-id-↑↑-v ε x refl = refl
wk<>-id-↑↑-v (Γ′ , A) vz Γ≡ 
  = var≡ (refl ++≡ Γ≡) (semwk≡ ⟦ refl ++≡ Γ≡′ ⟧c≡ Asem≡ Asem≡) 
         (vz≡ (refl ++≡ Γ≡′) A≡)
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk<>-id-↑↑ Γ′ A Γ≡′
        Asem≡ = ⟦⟧T≡ (refl ++≡ (,proj≡₁ Γ≡)) A≡
wk<>-id-↑↑-v (Γ′ , A) (vs {B = B} x) Γ≡ 
  = []wtm≡ (refl ++≡ Γ≡′) (refl ++≡ Γ≡) B≡ (wk≡ (refl ++≡ Γ≡′) A≡) 
           (wk<>-id-↑↑-v Γ′ x Γ≡′)
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk<>-id-↑↑ Γ′ A Γ≡′
        B≡ = wk<>-id-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡′ ]p
  
wk-comm-↑↑w-v ε x refl = refl
wk-comm-↑↑w-v (Γ′ , A) vz Γ≡ = vz≡ (refl ++≡ Γ≡′) A≡
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk-comm-↑↑w Γ′ A Γ≡′
wk-comm-↑↑w-v (Γ′ , A) (vs {B = B} x) Γ≡ 
  = vs≡ (refl ++≡  Γ≡′) A≡ B≡ (wk-comm-↑↑w-v Γ′ x Γ≡′)
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk-comm-↑↑w Γ′ A Γ≡′
        B≡ = wk-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡′ ]p

wk-comm-↑↑s-v ε x refl = refl
wk-comm-↑↑s-v (Γ′ , A) vz Γ≡
  = var≡ (refl ++≡ Γ≡) (semwk≡ ⟦ refl ++≡ Γ≡′ ⟧c≡ Asem≡ Asem≡) 
         (vz≡ (refl ++≡ Γ≡′) A≡)
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk-comm-↑↑s Γ′ A Γ≡′
        Asem≡ = ⟦⟧T≡ (refl ++≡ (,proj≡₁ Γ≡)) A≡
wk-comm-↑↑s-v (Γ′ , A) (vs {B = B} x) Γ≡ 
  = trans xi≡ refl x≡ (sym swap)
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = wk-comm-↑↑s Γ′ A Γ≡′
        B≡ = wk-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡′ ]p
        x≡ = []wtm≡ (refl ++≡ Γ≡′) (refl ++≡ Γ≡) B≡ (wk≡ (refl ++≡ Γ≡′) A≡) 
                    (wk-comm-↑↑s-v Γ′ x Γ≡′)
        swap = wk-comm-↑↑w-tm ε (x [ _ ↑↑s Γ′ ]sv) refl
        xi≡ = Tm≡ (refl ++≡ Γ≡)
                  ([]sem≡ ⟦ refl ++≡ Γ≡ ⟧c≡ ⟦ refl ++≡ Γ≡′ ⟧c≡ B≡
                  (⟦⟧w≡ (refl ++≡ Γ≡) (refl ++≡ Γ≡′) (wk≡ (refl ++≡ Γ≡′) A≡)))

<>-comm-↑↑w-v ε vz refl = refl
<>-comm-↑↑w-v ε (vs x) refl = refl
<>-comm-↑↑w-v (Γ′ , A) vz Γ≡ 
  = var≡ (refl ++≡ Γ≡) (semwk≡ ⟦ refl ++≡ Γ≡′ ⟧c≡ Asem≡ Asem≡) 
         (vz≡ (refl ++≡ Γ≡′) A≡)
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = <>-comm-↑↑w Γ′ A Γ≡′
        Asem≡ = ⟦⟧T≡ (refl ++≡ (,proj≡₁ Γ≡)) A≡
<>-comm-↑↑w-v (Γ′ , A) (vs {B = B} x) Γ≡
  = trans refl xi≡ swap x≡
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡  = <>-comm-↑↑w Γ′ A Γ≡′
        B≡ = <>-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡′ ]p
        swap = wk-comm-↑↑w-tm ε (x [ < _ > ↑↑s Γ′ ]sv) refl 
        x≡ = []wtm≡ (refl ++≡ Γ≡′) (refl ++≡ Γ≡) B≡ (wk≡  (refl ++≡ Γ≡′) A≡)      
                    (<>-comm-↑↑w-v Γ′ x Γ≡′)
        xi≡ = Tm≡ (refl ++≡ Γ≡)
                  ([]sem≡ ⟦ refl ++≡ Γ≡ ⟧c≡ ⟦ refl ++≡ Γ≡′ ⟧c≡ B≡
                  (⟦⟧w≡ (refl ++≡ Γ≡) (refl ++≡ Γ≡′) (wk≡ (refl ++≡ Γ≡′) A≡)))

<>-comm-↑↑s-v ε vz refl = refl
<>-comm-↑↑s-v ε (vs x) refl = sym (wk<>-id-↑↑-tm ε _ refl)
<>-comm-↑↑s-v (Γ′ , A) vz Γ≡ 
  = var≡ (refl ++≡ Γ≡) (semwk≡ ⟦ refl ++≡ Γ≡′ ⟧c≡ Asem≡ Asem≡) 
         (vz≡ (refl ++≡ Γ≡′) A≡)
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡ = <>-comm-↑↑s Γ′ A Γ≡′
        Asem≡ = ⟦⟧T≡ (refl ++≡ (,proj≡₁ Γ≡)) A≡
<>-comm-↑↑s-v (Γ′ , A) (vs {B = B} x) Γ≡
  = trans refl xi≡ lhs-swap (trans xi≡ refl x≡ (sym rhs-swap))
  where Γ≡′ = ,proj≡₁ Γ≡
        A≡  = <>-comm-↑↑s Γ′ A Γ≡′
        B≡ = <>-comm-↑↑-sem ⟦ Γ′ ⟧tys B [ ⟦⟧tys≡ refl Γ≡′ ]p
        lhs-swap = wk-comm-↑↑s-tm ε (x [ < _ > ↑↑s Γ′ ]sv) refl 
        rhs-swap =  wk-comm-↑↑s-tm ε (x [ _ ↑↑s Γ′ ]sv) refl
        x≡ = []wtm≡ (refl ++≡ Γ≡′) (refl ++≡ Γ≡) B≡ (wk≡ (refl ++≡ Γ≡′) A≡) 
                    (<>-comm-↑↑s-v Γ′ x Γ≡′) 
        xi≡ = Tm≡ (refl ++≡ Γ≡)
                  ([]sem≡ ⟦ refl ++≡ Γ≡ ⟧c≡ ⟦ refl ++≡ Γ≡′ ⟧c≡ B≡
                  (⟦⟧w≡ (refl ++≡ Γ≡) (refl ++≡ Γ≡′) (wk≡ (refl ++≡ Γ≡′) A≡)))
