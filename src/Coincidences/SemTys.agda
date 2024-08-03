{-# OPTIONS --prop --show-irrelevant --rewriting #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys

module Coincidences.SemTys where

infixl 100 _[_]semtys

data SemTys : SemCtx → Set₁

_++s_ : ∀ Γ → SemTys Γ → SemCtx

data SemTys where
  ε   : ∀ {Γ} → SemTys Γ
  _,_ : ∀ {Γ} Γ′ → SemTy (Γ ++s Γ′) → SemTys Γ

Γ ++s ε = Γ
Γ ++s (Γ′ , A) = (Γ ++s Γ′) ,s A

_[_]semtys : ∀ {Γ Δ} → SemTys Γ → SemSub Δ Γ → SemTys Δ
_↑↑sem_ : ∀ {Γ Δ} (δ : SemSub Δ Γ) Γ′ → SemSub (Δ ++s Γ′ [ δ ]semtys) (Γ ++s Γ′)

ε [ δ ]semtys = ε
(Γ′ , A) [ δ ]semtys = Γ′ [ δ ]semtys , A ∘ (δ ↑↑sem Γ′)

δ ↑↑sem ε = δ
δ ↑↑sem (Γ′ , A) = (δ ↑↑sem Γ′) ↑s A

⟦_⟧tys : Tys Γ → SemTys ⟦ Γ ⟧c

⟦++⟧tys≡ : ∀ (Γ′ : Tys Γ) → ⟦ Γ ++ Γ′ ⟧c ≡ ⟦ Γ ⟧c ++s ⟦ Γ′ ⟧tys

⟦ ε ⟧tys = ε
⟦ Γ′ , A ⟧tys = ⟦ Γ′ ⟧tys , (subst SemTy (⟦++⟧tys≡ Γ′) ⟦ A ⟧T)

⟦⟧tys≡ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′} (Γ≡ : Γ₁ ≡ Γ₂) → Γ₁′ ≡[ cong Tys Γ≡ ]≡ Γ₂′ 
        → ⟦ Γ₁′ ⟧tys ≡[ cong SemTys ⟦ Γ≡ ⟧c≡ ]≡ ⟦ Γ₂′ ⟧tys
⟦⟧tys≡ refl refl = refl

⟦++⟧tys≡ ε = refl
⟦++⟧tys≡ (Γ′ , A) = Γ≡′ ,s≡ from-coe≡ (SemTy≡ Γ≡′) refl
  where Γ≡′ = ⟦++⟧tys≡ Γ′

-- This rewrite currently fails the confluence check due to there being no 
-- semantic build/shift operations yet. Implementing these would not be hard 
-- but, in practice, we never use build/shift and semantic types together so we 
-- can ignore this for now
{-# REWRITE ⟦++⟧tys≡ #-}


-- buildsem≡ : ∀ Γ → εsem ++s ⟦ build Γ ⟧tys ≡ ⟦ Γ ⟧c
-- buildsem≡ ε = refl
-- buildsem≡ (Γ , A) = sym (dcong₂ _,s_ (sym (buildsem≡ Γ)) {!!})


-- shiftsem≡ : ∀ (Γ′ : Tys (Γ , A)) 
--           → (⟦ Γ ⟧c ,s ⟦ A ⟧T) ++s ⟦ Γ′ ⟧tys ≡ ⟦ Γ ⟧c ++s ⟦ shift A Γ′ ⟧tys 


-- shiftsem≡ ε = refl
-- shiftsem≡ (Γ′ , A) = foo ∙ {!!}
--   where Γ≡ = shiftsem≡ Γ′
--         foo = dcong₂ _,s_ (shiftsem≡ Γ′) (erefl (subst SemTy Γ≡ ⟦ A ⟧T))
