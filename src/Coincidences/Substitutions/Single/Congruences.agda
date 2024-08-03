{-# OPTIONS --rewriting --prop --show-irrelevant #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys
open import Coincidences.SemTys
open import Coincidences.Substitutions.Single.Weak
open import Coincidences.Substitutions.Single.Sub

-- TODO: Really we should sprinkle these congruences into the modules where
-- these things were originally defined instead of just defining a massive batch
-- of them randomly inside the module for single substitutions.
module Coincidences.Substitutions.Single.Congruences where

Tys≡ = cong Tys
SemTys≡ = cong SemTys
Wk≡ = cong₂ Wk
Sub≡ = cong₂ Sub

_++≡_ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′} (Γ≡ : Γ₁ ≡ Γ₂) → Γ₁′ ≡[ Tys≡ Γ≡ ]≡ Γ₂′
     → Γ₁ ++ Γ₁′ ≡ Γ₂ ++ Γ₂′
refl ++≡ refl = refl

,tys≡ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) 
          (Γ≡′ : Γ₁′ ≡[ Tys≡ Γ≡ ]≡ Γ₂′)
     → A₁ ≡[ Ty≡ (Γ≡ ++≡ Γ≡′) ]≡ A₂ → Γ₁′ , A₁ ≡[ Tys≡ Γ≡ ]≡ Γ₂′ , A₂ 
,tys≡ refl refl refl = refl

_++s≡_ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′} (Γ≡ : Γ₁ ≡ Γ₂) → Γ₁′ ≡[ SemTys≡ Γ≡ ]≡ Γ₂′
     → Γ₁ ++s Γ₁′ ≡ Γ₂ ++s Γ₂′
refl ++s≡ refl = refl

,semtys≡ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) 
          (Γ≡′ : Γ₁′ ≡[ SemTys≡ Γ≡ ]≡ Γ₂′)
     → A₁ ≡[ SemTy≡ (Γ≡ ++s≡ Γ≡′) ]≡ A₂ → Γ₁′ , A₁ ≡[ SemTys≡ Γ≡ ]≡ Γ₂′ , A₂ 
,semtys≡ refl refl refl = refl

,proj≡₁ : ∀ {Γ Γ₁′ Γ₂′} {A₁ : Ty (Γ ++ Γ₁′)} {A₂ : Ty (Γ ++ Γ₂′)} 
     → Tys._,_ Γ₁′ A₁ ≡ Tys._,_ Γ₂′ A₂ → Γ₁′ ≡ Γ₂′
,proj≡₁ refl = refl

,proj≡s₁ : ∀ {Γ Γ₁′ Γ₂′} {A₁ : SemTy (Γ ++s Γ₁′)} {A₂ : SemTy (Γ ++s Γ₂′)} 
     → SemTys._,_ Γ₁′ A₁ ≡ SemTys._,_ Γ₂′ A₂ → Γ₁′ ≡ Γ₂′
,proj≡s₁ refl = refl

↑s≡ : ∀ {Γ₁ Γ₂ Δ δ₁ δ₂} {A : SemTy Δ} (Γ≡ : Γ₁ ≡ Γ₂)
          (δ≡ : δ₁ ≡[ SemSub≡ Γ≡ refl ]≡ δ₂) 
     → δ₁ ↑s A ≡[ SemSub≡ (Γ≡ ,s≡ ([]sem≡ Γ≡ refl (erefl A) δ≡)) refl 
     ]≡ δ₂ ↑s A
↑s≡ refl refl = refl 

[]w≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
     → A₁ ≡[ Ty≡ Γ≡ ]≡ A₂ → δ₁ ≡[ Wk≡ Δ≡ Γ≡ ]≡ δ₂
     → A₁ [ δ₁ ]w ≡[ Ty≡ Δ≡ ]≡ A₂ [ δ₂ ]w
[]w≡ refl refl refl refl = refl

[]s≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
     → A₁ ≡[ Ty≡ Γ≡ ]≡ A₂ → δ₁ ≡[ Sub≡ Δ≡ Γ≡ ]≡ δ₂
     → A₁ [ δ₁ ]s ≡[ Ty≡ Δ≡ ]≡ A₂ [ δ₂ ]s
[]s≡ refl refl refl refl = refl

⟦⟧w≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
     → δ₁ ≡[ Wk≡ Γ≡ Δ≡ ]≡ δ₂ 
     → ⟦ δ₁ ⟧w ≡[ SemSub≡ ⟦ Γ≡ ⟧c≡ ⟦ Δ≡ ⟧c≡ ]≡ ⟦ δ₂ ⟧w
⟦⟧w≡ refl refl refl = refl

⟦⟧s≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
     → δ₁ ≡[ Sub≡ Γ≡ Δ≡ ]≡ δ₂ 
     → ⟦ δ₁ ⟧s ≡[ SemSub≡ ⟦ Γ≡ ⟧c≡ ⟦ Δ≡ ⟧c≡ ]≡ ⟦ δ₂ ⟧s
⟦⟧s≡ refl refl refl = refl

[]wtm≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ M₁ M₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
          (A≡ : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂) (δ≡ : δ₁ ≡[ Wk≡ Δ≡ Γ≡ ]≡ δ₂)
     → M₁ ≡[ Tm≡ Γ≡ A≡ ]≡ M₂
     → M₁ [ δ₁ ]wtm ≡[ Tm≡ Δ≡ ([]sem≡ ⟦ Δ≡ ⟧c≡ ⟦ Γ≡ ⟧c≡ A≡ (⟦⟧w≡ Δ≡ Γ≡ δ≡)) 
     ]≡ M₂ [ δ₂ ]wtm
[]wtm≡ refl refl refl refl refl = refl

[]stm≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ M₁ M₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
          (A≡ : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂) (δ≡ : δ₁ ≡[ Sub≡ Δ≡ Γ≡ ]≡ δ₂)
     → M₁ ≡[ Tm≡ Γ≡ A≡ ]≡ M₂
     → M₁ [ δ₁ ]stm ≡[ Tm≡ Δ≡ ([]sem≡ ⟦ Δ≡ ⟧c≡ ⟦ Γ≡ ⟧c≡ A≡ (⟦⟧s≡ Δ≡ Γ≡ δ≡)) 
     ]≡ M₂ [ δ₂ ]stm
[]stm≡ refl refl refl refl refl = refl

wk≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
     → wk ≡[ Wk≡ (Γ≡ ,≡ A≡) Γ≡ ]≡ wk 
wk≡ refl refl = refl
