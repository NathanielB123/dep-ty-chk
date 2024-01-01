-- {-# OPTIONS --show-implicit #-}
-- Temporary
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

open import 1Lab.Path using 
  (_≡_; subst; ap; refl; transport-refl; _∙_; ~_; coe0→1; _∨_; _∧_; Path
  ; transport; i0; i1; sym; PathP; ap₂; _∙P_; apd; PathP≡Path⁻; PathP≡Path
  ; transport-filler
  )
open import 1Lab.Path.Cartesian using (I-interp)
open import 1Lab.Type using (Type; lsuc; _⊔_; _$_; ¬_; absurd; ⊤; ⊥; tt; _∘_)
open import 1Lab.HLevel using (is-set; is-set→squarep)
open import Data.Dec using (Discrete; Dec)
open import 1Lab.Path.IdentitySystem using (set-identity-system)
open import Data.Id.Base using (_≡ᵢ_; reflᵢ; Id-identity-system)

open import DepTyChk.CubicalUtils using 
  (_≡[_]≡_; coe; map-idx; ∙refl; funky-ap; inl; inr; swap; USum
  ; subst-application
  )

-- Concrete syntax
module DepTyChk.Concrete where

infix 4 _∋_
infix 5 _∘ₛ_
infixl 5 _,_
infixr 6 _[_]T

data Ctx : Type
data Ty : Ctx → Type
data Subs : Ctx → Ctx → Type
data Tm : (Γ : Ctx) → Ty Γ → Type

{-# NO_POSITIVITY_CHECK #-}
data Ctx where
  ε      : Ctx
  _,_    : (Γ : Ctx) → Ty Γ → Ctx

,-inj₁ : ∀ {Γ Δ A B} → Γ , A ≡ Δ , B → Γ ≡ Δ
,-inj₁ p = ap (λ where
  ε       → ε
  (Γ , _) → Γ) p

ε,-diverge : Ctx → Type
ε,-diverge ε = ⊥
ε,-diverge (_ , _) = ⊤

,ε-disjoint : ∀ {Γ A} → ¬ Γ , A ≡ ε
,ε-disjoint p = coe (ap ε,-diverge p) tt

weaken : ∀ {Γ A} → Ty Γ → Ty (Γ , A)
substitute : ∀ {Γ A} → Ty (Γ , A) → Tm Γ A → Ty Γ

data Ty where
  U     : ∀ {Γ} → Ty Γ
  El    : ∀ {Γ} → Tm Γ U → Ty Γ
  Π     : ∀ {Γ} → (A : Ty Γ) → Ty (Γ , A) → Ty Γ

data _∋_ : (Γ : Ctx) → Ty Γ → Type where
  here : ∀ {Γ A} → Γ , A ∋ weaken A 
  there : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ weaken A

data Tm where
  lam : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
  -- app : ∀ {Γ A B C} → Tm Γ (Π A B) → (N : Tm Γ A) → C ≡ substitute B N → Tm Γ C
  var : ∀ {Γ A}   → Γ ∋ A → Tm Γ A

-- A single substitution
data Sub : Ctx → Ctx → Type

-- A single weakening
data Wk : Ctx → Ctx → Type

_[_]T : ∀ {Γ Δ} → Ty Δ → Subs Γ Δ → Ty Γ
_[_]t : ∀ {Γ Δ A} → Tm Δ A → (δ : Subs Γ Δ) → Tm Γ (A [ δ ]T)

_[_]T-sub : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]t-sub : ∀ {Γ Δ A} → Tm Δ A → (δ : Sub Γ Δ) → Tm Γ (A [ δ ]T-sub)
_[_]v-sub : ∀ {Γ Δ A} → Δ ∋ A → (δ : Sub Γ Δ) → Tm Γ (A [ δ ]T-sub)

_[_]T-wk : ∀ {Γ Δ} → Ty Δ → Wk Γ Δ → Ty Γ
_[_]t-wk : ∀ {Γ Δ A} → Tm Δ A → (δ : Wk Γ Δ) → Tm Γ  (A [ δ ]T-wk)
{-# TERMINATING #-}
_[_]v-wk : ∀ {Γ Δ A} → Δ ∋ A → (δ : Wk Γ Δ) → Γ ∋ A [ δ ]T-wk

-- We split substitutions up quite finely in order to try and prove termination
data Wk where
  wk  : ∀ {Γ A} → Wk (Γ , A) Γ
  _↑_ : ∀ {Γ Δ} → (δ : Wk Γ Δ) (A : Ty Δ) → Wk (Γ , A [ δ ]T-wk) (Δ , A)

data Sub where
  <_> : ∀ {Γ A} → (M : Tm Γ A) → Sub Γ (Γ , A) 
  _↑_ : ∀ {Γ Δ} → (δ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , A [ δ ]T-sub) (Δ , A)

data Subs where
  idₛ     : ∀ {Γ} → Subs Γ Γ
  sub-and : ∀ {Γ Δ Σ} → Sub Δ Σ → Subs Γ Δ → Subs Γ Σ
  wk-and  : ∀ {Γ Δ Σ} → Wk Δ Σ → Subs Γ Δ → Subs Γ Σ
  wk<>    : ∀ {Γ Δ A} {M : Tm Δ A} (δ : Subs Γ Δ) 
          → wk-and wk (sub-and < M > δ) ≡ δ
  wk↑     : ∀ {Γ Δ Σ A} (δ : Wk Γ Δ) (σ : Subs Σ _) 
          → wk-and wk (wk-and (δ ↑ A) σ) ≡ wk-and δ (wk-and wk σ)
  wk↑′    : ∀ {Γ Δ Σ A} (δ : Sub Γ Δ) (σ : Subs Σ _) 
          → wk-and wk (sub-and (δ ↑ A) σ) ≡ sub-and δ (wk-and wk σ)

weaken A = A [ wk ]T-wk
substitute A M = A [ < M > ]T-sub

U [ δ ]T-wk = U
El A [ δ ]T-wk = El (A [ δ ]t-wk)
Π A B [ δ ]T-wk =  Π (A [ δ ]T-wk) (B [ δ ↑ A ]T-wk)

U [ δ ]T-sub = U
El A [ δ ]T-sub = El (A [ δ ]t-sub)
Π A B [ δ ]T-sub = Π (A [ δ ]T-sub) (B [ δ ↑ A ]T-sub)

lam {A = A} M [ δ ]t-wk = lam {A = A [ δ ]T-wk} (M [ δ ↑ _ ]t-wk)
-- app M N p [ δ ]t-wk = app (M [ δ ]t-wk) (N [ δ ]t-wk) {!ap (_[ δ ]T-wk) p!}
var x [ δ ]t-wk = var (x [ δ ]v-wk)

lam M [ δ ]t-sub = lam (M [ δ ↑ _ ]t-sub)
-- app {B = U} M N p [ δ ]t-sub 
--   = app (M [ δ ]t-sub) (N [ δ ]t-sub) (ap (_[ δ ]T-sub) p)
-- app {B = El x} M N p [ δ ]t-sub 
--   = app (M [ δ ]t-sub) (N [ δ ]t-sub) {!ap (_[ δ ]T-sub) p!}
-- app {B = Π B B₁} M N p [ δ ]t-sub 
--   = app (M [ δ ]t-sub) (N [ δ ]t-sub) {!   !}
var x [ δ ]t-sub = x [ δ ]v-sub

A [ idₛ ]T = A
A [ sub-and δ σ ]T = A [ δ ]T-sub [ σ ]T
A [ wk-and δ σ ]T = A [ δ ]T-wk [ σ ]T
A [ wk<> δ i ]T = {!!}
A [ wk↑ δ σ i ]T = {!!}
A [ wk↑′ δ σ i ]T = {!!}

A [ idₛ ]t = A
A [ sub-and δ σ ]t = A [ δ ]t-sub [ σ ]t
A [ wk-and δ σ ]t = A [ δ ]t-wk [ σ ]t
A [ wk<> δ i ]t = {!!}
A [ wk↑ δ σ i ]t = {!!}
A [ wk↑′ δ σ i ]t = {!!}

x [ wk ]v-wk = there x
here [ δ ↑ A ]v-wk 
  = subst (_ ∋_) (ap (A [_]T) (sym (wk↑ δ idₛ))) here
there {A = A} x [ δ ↑ _ ]v-wk 
  = subst (_ ∋_) (ap (A [_]T) (sym (wk↑ δ idₛ))) (x [ δ ]v-wk [ wk ]v-wk)

here {A = A} [ < M > ]v-sub 
  = subst (Tm _) (ap (A [_]T) (sym (wk<> idₛ))) M
there {A = A} x [ < M > ]v-sub 
  = subst (Tm _) (ap (A [_]T) (sym (wk<> idₛ))) (var x)
here [ δ ↑ A ]v-sub
  = subst (Tm _) (ap (A [_]T) (sym (wk↑′ δ idₛ))) (var here)
there {A = A} x [ δ ↑ _ ]v-sub
  -- The call to t-weak here is fine because none of the -weak substitution
  -- helpers ever call a -sub one
  = subst (Tm _) (ap (A [_]T) (sym (wk↑′ δ idₛ))) (x [ δ ]v-sub [ wk ]t-wk)

_∘ₛ_ : ∀ {Γ Δ Σ} → Subs Δ Σ → Subs Γ Δ → Subs Γ Σ
idₛ ∘ₛ σ = σ
wk-and δ σ ∘ₛ γ = wk-and δ (σ ∘ₛ γ)
sub-and δ σ ∘ₛ γ = sub-and δ (σ ∘ₛ γ)
wk<> δ i ∘ₛ σ = {!!}
wk↑ δ σ i ∘ₛ γ = {!!}
wk↑′ δ σ i ∘ₛ γ = {!!}
 