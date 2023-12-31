-- {-# OPTIONS --show-implicit #-}

open import 1Lab.Path 
  using (_≡_; subst; ap; refl; transport-refl; _∙_; ~_; coe0→1; _∨_; _∧_; Path
  ; transport; i0; i1; sym; PathP; ap₂; _∙P_; apd)
open import 1Lab.Path.Cartesian using (I-interp)
open import 1Lab.Type using (Type; lsuc; _⊔_; _$_; ¬_; absurd; ⊤; ⊥; tt; _∘_)
open import 1Lab.HLevel using (is-set; is-set→squarep)
open import Data.Dec using (Discrete; Dec)
open import 1Lab.Path.IdentitySystem using (set-identity-system)
open import Data.Id.Base using (_≡ᵢ_; reflᵢ; Id-identity-system)

open import DepTyChk.CubicalUtils using (_≡[_]≡_; coe; map-idx; ∙refl)

-- Concrete syntax
module DepTyChk.Concrete where

infix 4 _∋_
infix 5 _∘ₛ_
infixl 5 _,_
infixr 6 _[_]T

data Ctx : Type
data Ty : Ctx → Type
data Sub : Ctx → Ctx → Type
data Tm : (Γ : Ctx) → Ty Γ → Type

{-# NO_POSITIVITY_CHECK #-}
data Ctx where
  ε      : Ctx
  _,_    : (Γ : Ctx) → Ty Γ → Ctx
  -- I'm pretty sure we could derive this but I don't know HoTT well enough
  -- squash : is-set Ctx

-- _≡?-Ctx_ :

-- We want f(i, 0) = 0 | 1
--         f(i, 1) = 0 | 1
--         f(0, j) = j
--         f(1, j) = 0 | 1

-- We need to somehow reason using the fact that the only way to identify ε with
-- itself is refl
-- squash-Ctx′ : ∀ (Γ : Ctx) (p : Γ ≡ Γ) → p ≡ refl 
-- squash-Ctx′ ε p i j = {!p j!}

squash-Ctx : is-set Ctx
squash-Ctx Γ Δ p₁ p₂ = {!!}

,-inj₁ : ∀ {Γ Δ A B} → Γ , A ≡ Δ , B → Γ ≡ Δ
,-inj₁ p = {!!}

,ε-disjoint : ∀ {Γ A} → ¬ Γ , A ≡ ε
,ε-disjoint = {!!}

weaken : ∀ {Γ A} → Ty Γ → Ty (Γ , A)

_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]t : ∀ {Γ Δ A} → Tm Δ A → (δ : Sub Γ Δ) → Tm Γ (A [ δ ]T)

data Ty where
  U     : ∀ {Γ} → Ty Γ
  El    : ∀ {Γ} → Tm Γ U → Ty Γ
  Π     : ∀ {Γ} → (A : Ty Γ) → Ty (Γ , A) → Ty Γ

data _∋_ : (Γ : Ctx) → Ty Γ → Type where
  here : ∀ {Γ A} → Γ , A ∋ weaken A 
  there : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ weaken A

data Tm where
  lam : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
  app : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ , A) B
  var : ∀ {Γ A}   → Γ ∋ A → Tm Γ A

tail : ∀ {Γ Δ A} → Sub Γ (Δ , A) → Sub Γ Δ
head  : ∀ {Γ Δ A} → (δ : Sub Γ (Δ , A)) → Tm Γ (A [ tail δ ]T)

-- Ugly forward references
idₛ : ∀ {Γ} → Sub Γ Γ
[id]T : ∀ {Γ} {A : Ty Γ} → A [ idₛ ]T ≡ A

-- Constructors inspired by 
-- https://www.cse.chalmers.se/~nad/publications/danielsson-types2006.pdf
data Sub where
  ε     : Sub ε ε
  _∘ₛ_  : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  wk    : ∀ {Γ A} → Sub (Γ , A) Γ
  _↑_   : ∀ {Γ Δ} → (δ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , A [ δ ]T) (Δ , A)
  <_>   : ∀ {Γ A} → (M : Tm Γ A) → Sub Γ (Γ , A) 
  -- Sub
  idl   : ∀ {Γ Δ} {δ : Sub Γ Δ} → idₛ ∘ₛ δ ≡ δ
  idr   : ∀ {Γ Δ} {δ : Sub Γ Δ} → δ ∘ₛ idₛ ≡ δ
  ass   : ∀ {Γ Δ Σ Ξ} {δ : Sub Σ Ξ} {σ : Sub Δ Σ} {γ : Sub Γ Δ}
        → (δ ∘ₛ σ) ∘ₛ γ ≡ δ ∘ₛ (σ ∘ₛ γ)
  -- idₛ   : ∀ {Γ}     → Sub Γ Γ
  -- ↑id   : ∀ {Γ} {A : Ty Γ} → PathP (λ i → ap (λ x → Sub (Γ , x) (Γ , A)) 
  --           {x = A [ id-fwd ]T} {y = A} [id]T i) (idₛ ↑ A) idₛ
  -- Truncate
  squash : ∀ {Γ Δ} → is-set (Sub Γ Δ)

-- Note we might be able to be slightly stricter about the forms of 
-- substitutions, by making idₛ computational down to a εₛ constructor
-- This eliminates the need for ↑id!
postulate εₛ : Sub ε ε

data is-id : ∀ {Γ} → Sub Γ Γ → Type

[id]T′ : ∀ {Γ} {A : Ty Γ} {δ : Sub Γ Γ} → is-id δ → A [ δ ]T ≡ A

data is-id where
  ε   : is-id ε
  _↑_ : ∀ {Γ} {δ : Sub Γ Γ} (p : is-id δ) (A : Ty Γ) 
      → is-id (subst (λ x → Sub (_ , x) _) ([id]T′ p) (δ ↑ A))

record IdSub (Γ : Ctx) : Type where
  constructor _,_
  pattern
  field
    δ : Sub Γ Γ
    p : is-id δ

id-sub : ∀ Γ → IdSub Γ
id-sub ε = ε , ε
id-sub (Γ , A) with id-sub Γ
... | δ , p = subst (λ x → Sub (_ , x) _) ([id]T′ p) (δ ↑ A) , p ↑ A

idₛ {Γ} with id-sub Γ
... | δ , _ = δ

-- We would like to define tail as:
-- tail idₛ = wk
-- tail (δ ∘ₛ σ) = tail δ ∘ₛ σ
-- tail wk = wk ∘ₛ wk
-- tail (δ ↑ A) = δ ∘ₛ wk
-- tail < M > = idₛ
-- But this relies on injectivity of _,_ (which Cubical Agda does not yet
-- support properly)
-- Therefore, we instead pass an explicit proof of index equality:


tail-compute : ∀ {Γ Δ Σ A} → Δ , A ≡ Σ → Sub Γ Σ → Sub Γ Δ
tail-compute p ε = absurd (,ε-disjoint p)
tail-compute p (δ ∘ₛ σ) = tail-compute p δ ∘ₛ σ
tail-compute p wk = subst (λ x → Sub x _) p wk ∘ₛ wk
tail-compute p (δ ↑ A) = subst (Sub _) (sym (,-inj₁ p)) δ ∘ₛ wk
tail-compute p < M > = subst (Sub _) (sym (,-inj₁ p)) idₛ
-- TODO: Boundary (confluence) conditions
tail-compute p (idl i) = {!   !}
tail-compute p (idr i) = {!   !}
tail-compute p (ass i) = {!!}
tail-compute p (squash δ σ α β i j) = {!   !}
-- tail-compute p idₛ = subst (λ x → Sub x _) p wk
-- tail-compute p (↑id i) = {!!}

tail = tail-compute refl  

-- Equations:


U [ δ ]T = U
El A [ δ ]T = El (A [ δ ]t)
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ↑ A ]T)


[][]T : ∀ {Γ Δ Σ A} {δ : Sub Δ Σ} {σ : Sub Γ Δ} 
      → A [ δ ]T [ σ ]T ≡ A [ δ ∘ₛ σ ]T
-- U[]   : ∀ {Γ Δ} {δ : Sub Γ Δ} → U [ δ ]T ≡ U
-- El[]  : ∀ {Γ Δ A} {δ : Sub Γ Δ} 
--       → El A [ δ ]T ≡ El (subst (Tm Γ) U[] (A [ δ ]t))
-- Π[]   : ∀ {Γ Δ A B} {δ : Sub Γ Δ} → Π A B [ δ ]T 
--       ≡ Π (A [ δ ]T) (B [ δ ↑ A ]T)
[id]t : ∀ {Γ A} {M : Tm Γ A} → M [ idₛ ]t ≡[ ap (Tm _) [id]T ]≡ M
-- I would have thought that this could follow from [id]t, but we get stuck 
-- on showing [id]T i ≡ U (we cannot match on 𝕀)
[id]t-U : ∀ {Γ} {M : Tm Γ U} → M [ idₛ ]t ≡ M
[][]t : ∀ {Γ Δ Σ A} {M : Tm Σ A} {δ : Sub Δ Σ} {σ : Sub Γ Δ}
      → M [ δ ]t [ σ ]t ≡[ ap (Tm _) ([][]T {δ = δ} {σ = σ}) ]≡ M [ δ ∘ₛ σ ]t 
-- hβ    : ∀ {Γ Δ A} {δ : Sub Γ Δ} {M : Tm Γ (A [ δ ]T)} 
--       → head (δ , M) ≡[ ap (Tm _ ∘ _[_]T A) tβ ]≡ M
-- Πβ    : ∀ {Γ A B} {M : Tm (Γ , A) B} → app (lam M) ≡ M
-- Πη    : ∀ {Γ A B} {M : Tm Γ (Π A B)} → lam (app M) ≡ M
-- lam[] : ∀ {Γ Δ A B} {δ : Sub Δ Γ} {M : Tm (Γ , A) B} 
--       → (lam M) [ δ ]t ≡[ ap (Tm _) Π[] 
--       ]≡ lam (M [ (δ ∘ₛ tail idₛ) , subst (Tm _) [][]T (head idₛ) ]t)

↑id   : ∀ {Γ} {A : Ty Γ} → PathP (λ i → ap (λ x → Sub (Γ , x) (Γ , A)) 
              {x = A [ idₛ ]T} {y = A} [id]T i) (idₛ ↑ A) idₛ

[id]T′ ε = {!!}
[id]T′ (p ↑ A) = {!!}

[id]T {A = U} = refl
[id]T {A = El A} = ap El [id]t-U
[id]T {A = Π A B} 
  = ap₂ Π [id]T 
  $ map-idx (_∙P_ {B = Ty ∘ (_ ,_)} (apd (λ _ → B [_]T) ↑id) [id]T) 
  $ ap (ap (Ty ∘ (_ ,_))) ∙refl

-- We also want the below equations to hold:
-- A [ idₛ ]T = A
-- A [ δ ∘ₛ σ ]T′ = A [ δ ]T [ σ ]T

-- M [ idₛ ]t = subst (Tm _) (sym [id]T) M
-- lam M [ δ ]t = {!   !}
-- app M [ δ ]t = {!   !}
-- var here [ δ ]t = {!   !}
-- var (there _) [ δ ]t = {!   !}
  