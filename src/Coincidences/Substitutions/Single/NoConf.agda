{-# OPTIONS --rewriting --prop #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys 
open import Coincidences.SemTys 
open import Coincidences.Substitutions.Single.Congruences
open import Coincidences.Substitutions.Single.Weak
open import Coincidences.Substitutions.Single.Sub

-- Agda complains that these rewrite rules aren't confluent. I'm not totally
-- convinced by Agda's reasoning as the case it comes up with for '⟦[]⟧wtys≡'
-- is covered exactly by '⟦↑↑w⟧≡' but I guess the problem is that the set
-- of rewrite rules is temporarily not confluent (i.e. between REWRITE pragmas).
--
-- The problem is that '⟦[]⟧wtys≡' and '⟦[]⟧stys≡' are only confluent if 
-- '⟦↑↑w⟧≡' and '⟦↑↑s⟧≡' are rewrite rules, but Agda can only see that '⟦↑↑w⟧≡' 
-- and '⟦↑↑s⟧≡' are valid rewrites once '⟦[]⟧wtys≡' and '⟦[]⟧stys≡' in place.
--
-- (Note we also have the same build/shift issues as mention in 'SemTys' but I 
-- am much less concerned by this)
module Coincidences.Substitutions.Single.NoConf where

⟦[]⟧wtys≡ : ∀ Γ′ (δ : Wk Δ Γ) 
          → ⟦ Γ′ [ δ ]wtys ⟧tys ≡ ⟦ Γ′ ⟧tys [ ⟦ δ ⟧w ]semtys
⟦[]⟧stys≡ : ∀ Γ′ (δ : Sub Δ Γ) 
          → ⟦ Γ′ [ δ ]stys ⟧tys ≡ ⟦ Γ′ ⟧tys [ ⟦ δ ⟧s ]semtys

⟦↑↑w⟧≡ : ∀ Γ′ (δ : Wk Δ Γ) 
      → ⟦ δ ↑↑w Γ′ ⟧w ≡[ SemSub≡ (refl ++s≡ ⟦[]⟧wtys≡ Γ′ δ) refl 
     ]≡ ⟦ δ ⟧w ↑↑sem ⟦ Γ′ ⟧tys
⟦↑↑s⟧≡ : ∀ Γ′ (δ : Sub Δ Γ) 
      → ⟦ δ ↑↑s Γ′ ⟧s ≡[ SemSub≡ (refl ++s≡ ⟦[]⟧stys≡ Γ′ δ) refl 
     ]≡ ⟦ δ ⟧s ↑↑sem ⟦ Γ′ ⟧tys

⟦[]⟧wtys≡ ε δ = refl
⟦[]⟧wtys≡ (Γ′ , A) δ 
  = ,semtys≡ refl δ≡ ([]sem≡ (refl ++s≡ δ≡) refl (erefl ⟦ A ⟧T) (⟦↑↑w⟧≡ Γ′ δ))
  where δ≡ = ⟦[]⟧wtys≡ Γ′ δ
⟦[]⟧stys≡ ε δ = refl
⟦[]⟧stys≡ (Γ′ , A) δ 
  = ,semtys≡ refl δ≡ ([]sem≡ (refl ++s≡ δ≡) refl (erefl ⟦ A ⟧T) (⟦↑↑s⟧≡ Γ′ δ))
  where δ≡ = ⟦[]⟧stys≡ Γ′ δ

⟦↑↑w⟧≡ ε δ = refl
⟦↑↑w⟧≡ (Γ′ , A) δ = ↑s≡ (refl ++s≡ ⟦[]⟧wtys≡ Γ′ δ) (⟦↑↑w⟧≡ Γ′ δ)
⟦↑↑s⟧≡ ε δ = refl
⟦↑↑s⟧≡ (Γ′ , A) δ = ↑s≡ (refl ++s≡ ⟦[]⟧stys≡ Γ′ δ) (⟦↑↑s⟧≡ Γ′ δ)

{-# REWRITE ⟦[]⟧wtys≡ ⟦[]⟧stys≡ #-}
{-# REWRITE ⟦↑↑w⟧≡ ⟦↑↑s⟧≡ #-}
