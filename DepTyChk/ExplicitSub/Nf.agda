open import 1Lab.Type using (Type; _∘_)
open import 1Lab.Path using (_≡_; refl; subst; sym; PathP; ap; apd; ap₂; i0; i1)

open import DepTyChk.CubicalUtils using (_≡[_]≡_; apd₂; eq-left; eq-right)

open import DepTyChk.ExplicitSub.Syntax

module DepTyChk.ExplicitSub.Nf where

data NfVar : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Type where
  vz : ∀ {Γ A} → NfVar (Γ , A) (A [ wk ]T) vz
  vs : ∀ {Γ A B x} → NfVar Γ A x → NfVar (Γ , B) (A [ wk ]T) (x [ wk ]t)

data NfApp : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Type

data Nf : (Γ : Ctx) (A : Ty Γ) → Tm Γ A → Type

data NfApp where
  var : ∀ {Γ A x} → NfVar Γ A x → NfApp Γ A x
  app : ∀ {Γ A B} {M : Tm Γ (Π A B)} {N : Tm Γ A} → NfApp Γ (Π A B) M → Nf Γ A N 
      → NfApp Γ (B [ < N > ]T) ((app M) [ < N > ]t)

data Nf where
  nfapp : ∀ {Γ A x} → NfApp Γ A x → Nf Γ A x
  lam   : ∀ {Γ A B M} → Nf (Γ , A) B M → Nf Γ (Π A B) (lam M)
