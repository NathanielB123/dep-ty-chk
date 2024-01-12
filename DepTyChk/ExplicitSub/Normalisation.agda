{-# OPTIONS -WnoUnsupportedIndexedMatch #-} 

open import 1Lab.Type using (Type; _∘_; _$_)
open import 1Lab.Path 
  using (_≡_; refl; subst; sym; PathP; ap; apd; ap₂; i0; i1; transport; symP)

open import DepTyChk.CubicalUtils 
  using (_≡[_]≡_; apd₂; eq-left; eq-right)

open import DepTyChk.ExplicitSub.Syntax
open import DepTyChk.ExplicitSub.Nf

module DepTyChk.ExplicitSub.Normalisation where

{-# TERMINATING #-}
nf : ∀ {Γ A} → (M : Tm Γ A) → Nf Γ A M
-- Normalisation by hereditary substitution (unclear if this is possible)
_[_]nf : ∀ {Γ Δ A M} → Nf Γ A M → (δ : Sub Δ Γ) → Nf Δ (A [ δ ]T) (M [ δ ]t)
_[_]nfapp : ∀ {Γ Δ A M} → NfApp Γ A M → (δ : Sub Δ Γ) → Nf Δ (A [ δ ]T) (M [ δ ]t)
-- Temporary - I think we might need to split weakenings and substitutions
-- again...
weaken : ∀ {Γ A B M} → NfApp Γ A M → NfApp (Γ , B) (A [ wk ]T) (M [ wk ]t)
_[_]nfv : ∀ {Γ Δ A M} → NfVar Γ A M → (δ : Sub Δ Γ) → Nf Δ (A [ δ ]T) (M [ δ ]t)


-- Nf (Γ , A) ((A₁ [ wk ↑ A ]T) [ < vz > ]T)
--       (app (M [ wk ]t) [ < vz > ]t)
--       ≡ Nf (Γ , A) A₁ (app M)
-- (λ i → Nf _ {!!} {!!})

nf (lam M) = lam (nf M)
nf (app M) with nf M
... | (nfapp M′) 
  = transport (apd₂ (λ _ → Nf _) (wk<vz>T _) (wk<vz>t′ M))
  $ nfapp (app (weaken M′) (nfapp (var vz)))
nf (app .(lam M)) | lam {M = M} M′ = subst (Nf _ _) (sym (β M)) M′
nf vz = nfapp (var vz)
nf (M [ δ ]t) = nf M [ δ ]nf
nf (wk<>↑↑t M i) = {!   !}
nf (wk↑↑t δ M i) = {!   !}
nf (lam[]t δ M i) = {!!}
nf (vz[<>]t δ i) = {!!}
nf (β M i) = {!!}
nf (η M i) = {!!}
nf (wk<vz>↑↑t M i) = {!!}
nf (vz[↑]t M i) = {!!}

nfapp M [ δ ]nf = M [ δ ]nfapp
lam M [ δ ]nf = subst (Nf _ _) (lam[]t δ _) (lam (M [ δ ↑ _ ]nf))

var x [ δ ]nfapp = x [ δ ]nfv
app M N [ δ ]nfapp = {!M [ δ ]nfapp!} -- We need to match on this...


x [ wk ]nfv = nfapp (var (vs x))
vz [ < M > ]nfv 
  = transport (apd₂ (λ _ → Nf _) (sym (wk<>T _)) (symP (vz[<>]t M))) (nf M) 
vz [ δ ↑ _ ]nfv 
  = transport (apd₂ (λ _ → Nf _) (sym (wk↑T δ _)) (symP (vz[↑]t δ))) 
  $ nfapp (var vz)
vs x [ < M > ]nfv 
  = transport (apd₂ (λ _ → Nf _) (sym (wk<>T _)) (symP (wk<>t _))) 
  $ nfapp (var x)
vs x [ δ ↑ _ ]nfv 
  = transport (apd₂ (λ _ → Nf _) (sym (wk↑T δ _)) (symP (wk↑t δ _)))
  $ x [ δ ]nfv [ wk ]nf