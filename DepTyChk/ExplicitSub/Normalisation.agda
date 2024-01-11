{-# OPTIONS -WnoUnsupportedIndexedMatch #-} 

open import 1Lab.Type using (Type; _∘_)
open import 1Lab.Path 
  using (_≡_; refl; subst; sym; PathP; ap; apd; ap₂; i0; i1; transport)

open import DepTyChk.CubicalUtils using (_≡[_]≡_; apd₂; eq-left; eq-right)

open import DepTyChk.ExplicitSub.Syntax
open import DepTyChk.ExplicitSub.Nf

module DepTyChk.ExplicitSub.Normalisation where


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
nf {A = A} (app {A = B} M) with nf M
... | (nfapp {A = A′} M′) = transport (λ i → Nf _ {!(wk<>↑↑T {Σ = ε , B} A i)!} {!!}) (nfapp (app (weaken M′) (nfapp (var vz))))
  where
    foo = nfapp (app (weaken M′) (nfapp (var vz))) -- (nfapp (var {!NfVar.vz!}))
nf (app .(lam M)) | lam {M = M} M′ = subst (Nf _ _) (sym (β M)) M′
nf vz = nfapp (var vz)
nf (M [ δ ]t) = nf M [ δ ]nf
nf (wk<>↑↑t M i) = {!   !}
nf (wk↑↑t δ M i) = {!   !}
nf (lam[]t δ M i) = {!!}
nf (vz[<>]t δ i) = {!!}
nf (β M i) = {!!}

nfapp M [ δ ]nf = M [ δ ]nfapp
lam M [ δ ]nf = subst (Nf _ _) (lam[]t δ _) (lam (M [ δ ↑ _ ]nf))

var x [ δ ]nfapp = {!   !}
app M N [ δ ]nfapp = {!   !}

vz [ wk ]nfv = {!   !}
vz [ < M > ]nfv = subst (Nf _ _) {!!} (nf (subst (Tm _) (sym (wk<>T _)) M))
  -- where
  --   foo = nf (subst (Tm _) (sym (wk<>T _)) M)
vz [ δ ↑ _ ]nfv = {!   !}
vs M [ δ ]nfv = {!!}

-- _[_]t′ : ∀ {Γ Δ A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T)
-- lam M [ δ ]t′ = lam (M [ δ ↑ _ ]t′)
-- When considering normal forms, I believe this case should be impossible;
-- though I admit my intuition for categorical application might be slightly
-- lacking
-- app {A = B} M [ wk {A = C} ]t′ = {!!}
-- app M [ < N > ]t′ = app M [ < N > ]t
-- app M [ δ ↑ _ ]t′ = app (M [ δ ]t′)
-- vz [ wk ]t′ = vz [ wk ]t
-- vz [ < M > ]t′ = subst (Tm _) (sym (wk<>T _)) M
-- vz [ δ ↑ _ ]t′ = subst (Tm _) (sym (wk↑↑T δ _)) vz
-- (M [ σ ]t) [ δ ]t′ = {!   !}
-- wk<>↑↑t M i [ δ ]t′ = {!   !}
-- wk↑↑t σ M i [ δ ]t′ = {!   !}
-- lam M [ δ ]t′ = {!   !} 
-- app M [ δ ]t′ = {!   !}  
-- vz [ wk ]t′ = {!   !}
-- vz [ < M > ]t′ = subst (Tm _) (sym (wk<>T _)) M
-- vz [ δ ↑ _ ]t′ = {!vz!}     
-- (M [ σ ]t) [ δ ]t′ = M [ σ ]t [ δ ]t
-- wk<>↑↑t M i [ δ ]t′ = {!   !}  