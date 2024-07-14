{-# OPTIONS --rewriting #-}

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; erefl; cong; cong₂)

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Sub 

-- Some additional equations from Sub that, in Agda's implementation of
-- rewrite rules, break confluence
-- This feels like quite buggy behaviour to me, but maybe there is a reasonable
-- explanation
module Coincidences.SubNoConf where

-- Adding extra rewrites to make this confluent might be possible. I haven't
-- checked much.
funky : ∀ {Γ} {Γ₁′ Γ₂′ : SemTys Γ} {A₁ A₂} (Γ≡ : (Γ₁′ , A₁) ≡ (Γ₂′ , A₂)) 
          (A≡ : A₁ ≡[ SemTy≡ (refl ++s≡ ,proj≡s₁ Γ≡) ]≡ A₂)
      → (refl ++s≡ ,proj≡s₁ Γ≡) ,s≡ A≡ ≡ refl ++s≡ Γ≡
funky refl refl = refl

funky2 : ∀ {Γ₁′ Γ₂′ : Tys Γ} {A₁ A₂} (Γ≡ : (Γ₁′ , A₁) ≡ (Γ₂′ , A₂)) 
          (A≡ : A₁ ≡[ Ty≡ (refl ++≡ ,proj≡₁ Γ≡) ]≡ A₂) 
       → (refl ++≡ ,proj≡₁ Γ≡) ,≡ A≡ ≡ refl ++≡ Γ≡
funky2 refl refl = refl

{-# REWRITE funky funky2 #-}


⟦++⟧c≡β : ∀ {Γ₁′ Γ₂′ : Tys Γ} (Γ≡ : Γ₁′ ≡ Γ₂′) 
       → cong ⟦_⟧c (refl ++≡ Γ≡) ≡ refl ++s≡ ⟦ Γ≡ ⟧tys≡
⟦++⟧c≡β refl = refl

-- For some reason this rule breaks confluence
-- E.g: It doesn't apply to 
-- >  ∀ {Γ₁′ Γ₂′ : Tys Γ} {A₂} (Γ≡ : Γ₁′ ≡ (Γ₂′ , A₂)) 
-- >  → cong ⟦_⟧c (refl ++≡ Γ≡) ≡ refl ++s≡ ⟦ Γ≡ ⟧tys≡
-- This feels like a bug to me...
{-# REWRITE ⟦++⟧c≡β #-}

⟦,⟧tys≡β : ∀ {Γ₁′ Γ₂′ : Tys Γ} {A₁ A₂} (Γ≡ : Γ₁′ ≡ Γ₂′) 
             (A≡ : A₁ ≡[ Ty≡ (refl ++≡ Γ≡) ]≡ A₂)
         → ⟦ ,tys≡ Γ≡ A≡ ⟧tys≡ ≡ ,semtys≡ _ ⟦ Γ≡ ⟧tys≡ ⟦ A≡ ⟧T≡

⟦,⟧tys≡β refl refl = refl 

{-# REWRITE ⟦,⟧tys≡β #-}

⟦[]⟧wtys≡ : ∀ Γ′ (δ : Wk Δ Γ) 
          → ⟦ Γ′ [ δ ]wtys ⟧tys ≡ ⟦ Γ′ ⟧tys [ ⟦ δ ⟧w ]semtys
⟦[]⟧stys≡ : ∀ Γ′ (δ : Sub Δ Γ) 
          → ⟦ Γ′ [ δ ]stys ⟧tys ≡ ⟦ Γ′ ⟧tys [ ⟦ δ ⟧s ]semtys

⟦↑↑w⟧≡ : ∀ Γ′ (δ : Wk Δ Γ) 
      → ⟦ δ ↑↑w Γ′ ⟧w ≡[ SemSub≡ (refl ++s≡ (⟦[]⟧wtys≡ Γ′ δ)) refl 
     ]≡ ⟦ δ ⟧w ↑↑sem ⟦ Γ′ ⟧tys
⟦↑↑s⟧≡ : ∀ Γ′ (δ : Sub Δ Γ) 
      → ⟦ δ ↑↑s Γ′ ⟧s ≡[ SemSub≡ (refl ++s≡ (⟦[]⟧stys≡ Γ′ δ)) refl 
     ]≡ ⟦ δ ⟧s ↑↑sem ⟦ Γ′ ⟧tys

⟦[]⟧wtys≡ ε δ = refl
⟦[]⟧wtys≡ (Γ′ , A) δ 
  = ,semtys≡ _ (⟦[]⟧wtys≡ Γ′ δ) ([]sem≡ (erefl ⟦ A ⟧T) (⟦↑↑w⟧≡ Γ′ δ))
⟦[]⟧stys≡ ε δ = refl
⟦[]⟧stys≡ (Γ′ , A) δ 
  = ,semtys≡ _ (⟦[]⟧stys≡ Γ′ δ) ([]sem≡ (erefl ⟦ A ⟧T) (⟦↑↑s⟧≡ Γ′ δ))

⟦↑↑w⟧≡ ε δ = refl
⟦↑↑w⟧≡ (Γ′ , A) δ = ↑s≡ (refl ++s≡ ⟦[]⟧wtys≡ Γ′ δ) (⟦↑↑w⟧≡ Γ′ δ)
⟦↑↑s⟧≡ ε δ = refl
⟦↑↑s⟧≡ (Γ′ , A) δ = ↑s≡ (refl ++s≡ ⟦[]⟧stys≡ Γ′ δ) (⟦↑↑s⟧≡ Γ′ δ)

{-# REWRITE ⟦[]⟧wtys≡ ⟦[]⟧stys≡ #-}

⟦↑↑w⟧≡-rw : ∀ Γ′ (δ : Wk Δ Γ) 
          → ⟦ δ ↑↑w Γ′ ⟧w ≡ ⟦ δ ⟧w ↑↑sem ⟦ Γ′ ⟧tys
⟦↑↑w⟧≡-rw Γ′ δ = ≡[]≡-uip (⟦↑↑w⟧≡ Γ′ δ)

⟦↑↑s⟧≡-rw : ∀ Γ′ (δ : Sub Δ Γ) 
          → ⟦ δ ↑↑s Γ′ ⟧s ≡ ⟦ δ ⟧s ↑↑sem ⟦ Γ′ ⟧tys
⟦↑↑s⟧≡-rw Γ′ δ = ≡[]≡-uip (⟦↑↑s⟧≡ Γ′ δ)


{-# REWRITE ⟦↑↑w⟧≡-rw ⟦↑↑s⟧≡-rw #-}
   