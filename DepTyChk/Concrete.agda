-- {-# OPTIONS --show-implicit #-}

open import 1Lab.Path 
  using (_≡_; subst; ap; refl; transport-refl; _∙_; ~_; coe0→1; _∨_; _∧_; Path
  ; transport)
open import 1Lab.Path.Cartesian using (I-interp)
open import 1Lab.Type using (Type; lsuc; _⊔_; _$_; ¬_; absurd; ⊤; ⊥; tt; _∘_)
open import 1Lab.HLevel using (is-set; is-set→squarep)

open import DepTyChk.CubicalUtils using (_≡[_]≡_; coe)

-- Concrete syntax
module DepTyChk.Concrete where

infix 5 _∘ₛ_
infix 5 _,_
infixr 6 _[_]T

data Ctx : Type
Ty : Ctx → Type
Sub : Ctx → Ctx → Type
Tm : (Γ : Ctx) → Ty Γ → Type

{-# NO_POSITIVITY_CHECK #-}
data Ctx where
  ε      : Ctx
  _,_    : (Γ : Ctx) → Ty Γ → Ctx
  -- I'm pretty sure we could derive this but I don't know HoTT well enough
  squash : is-set Ctx

-- Universe of syntax types
data SynU : Type where
  SynTy : Ctx → SynU
  SynSub : Ctx → Ctx → SynU
  SynTm : (Γ : Ctx) → Ty Γ → SynU

Ty-diverge : SynU → Type
Ty-diverge (SynTy _) = ⊥
Ty-diverge (SynSub _ _) = ⊤
Ty-diverge (SynTm _ _) = ⊤

SubTy-disjoint : ∀ {Γ Δ Σ} → ¬ SynSub Δ Σ ≡ SynTy Γ
SubTy-disjoint p = coe (ap Ty-diverge p) tt

TmTy-disjoint : ∀ {Γ Δ A} → ¬ SynTm Δ A ≡ SynTy Γ
TmTy-disjoint p = coe (ap Ty-diverge p) tt

-- I find it quite ugly that we need to write cases for SynSub and SynTm here
-- when they clearly will not be entered - perhaps I could use funky-ap...
Ty-inj : ∀ {Γ Δ} → SynTy Γ ≡ SynTy Δ → Γ ≡ Δ
Ty-inj p = ap (λ where
  (SynTy Γ) → Γ
  (SynSub Γ _) → Γ
  (SynTm Γ _) → Γ) p 

data Syntax : SynU → Type

Ty Γ = Syntax (SynTy Γ)
Sub Γ Δ = Syntax (SynSub Γ Δ)
Tm Γ A = Syntax (SynTm Γ A)

_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ

data Syntax where
  -- Syntax
  -- Ty
  U     : ∀ {Γ}   → Ty Γ
  El    : ∀ {Γ}   → Tm Γ U → Ty Γ
  Π     : ∀ {Γ}   → (A : Ty Γ) → Ty (Γ , A) → Ty Γ
  -- _[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
  -- Sub
  ε     : ∀ {Γ}     → Sub Γ ε
  _,_   : ∀ {Γ Δ A} → (δ : Sub Γ Δ) → Tm Γ (A [ δ ]T) → Sub Γ (Δ , A)
  idₛ   : ∀ {Γ}     → Sub Γ Γ
  _∘ₛ_  : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  tail  : ∀ {Γ Δ A} → Sub Γ (Δ , A) → Sub Γ Δ
  -- Tm
  lam   : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
  app   : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ , A) B
  head  : ∀ {Γ Δ A} → (δ : Sub Γ (Δ , A)) → Tm Γ (A [ tail δ ]T)
  _[_]t : ∀ {Γ Δ A} → Tm Δ A → (δ : Sub Γ Δ) → Tm Γ (A [ δ ]T)
  -- Paths
  -- Ty
  [id]T : ∀ {Γ} {A : Ty Γ} → A [ idₛ ]T ≡ A
  [][]T : ∀ {Γ Δ Σ A} {δ : Sub Δ Σ} {σ : Sub Γ Δ} 
        → A [ δ ]T [ σ ]T ≡ A [ δ ∘ₛ σ ]T
  U[]   : ∀ {Γ Δ} {δ : Sub Γ Δ} → U [ δ ]T ≡ U
  El[]  : ∀ {Γ Δ A} {δ : Sub Γ Δ} 
        → El A [ δ ]T ≡ El (subst (Tm Γ) U[] (A [ δ ]t))
  Π[]   : ∀ {Γ Δ A B} {δ : Sub Γ Δ} → Π A B [ δ ]T 
        ≡ Π (A [ δ ]T) (B [ (δ ∘ₛ tail idₛ) , subst (Tm _) [][]T (head idₛ) ]T)
  -- Sub
  idl   : ∀ {Γ Δ} {δ : Sub Γ Δ} → idₛ ∘ₛ δ ≡ δ
  idr   : ∀ {Γ Δ} {δ : Sub Γ Δ} → δ ∘ₛ idₛ ≡ δ
  ass   : ∀ {Γ Δ Σ Ξ} {δ : Sub Σ Ξ} {σ : Sub Δ Σ} {γ : Sub Γ Δ}
        → (δ ∘ₛ σ) ∘ₛ γ ≡ δ ∘ₛ (σ ∘ₛ γ)
  ,∘    : ∀ {Γ Δ Σ A} {δ : Sub Γ Δ} {σ : Sub Σ Γ} {M : Tm Γ (A [ δ ]T)} 
        → (δ , M) ∘ₛ σ ≡ (δ ∘ₛ σ) , subst (Tm _) [][]T (M [ σ ]t)
  tβ    : ∀ {Γ Δ A} {δ : Sub Γ Δ} {M : Tm Γ (A [ δ ]T)} → tail (δ , M) ≡ δ
  ,η    : ∀ {Γ Δ A} {δ : Sub Γ (Δ , A)} → tail δ , head δ ≡ δ
  εη    : ∀ {Γ} {δ : Sub Γ ε} → δ ≡ ε
  -- Tm
  [id]t : ∀ {Γ A} {M : Tm Γ A} → M [ idₛ ]t ≡[ ap (Tm _) [id]T ]≡ M
  [][]t : ∀ {Γ Δ Σ A} {M : Tm Σ A} {δ : Sub Δ Σ} {σ : Sub Γ Δ}
        → M [ δ ]t [ σ ]t ≡[ ap (Tm _) [][]T ]≡ M [ δ ∘ₛ σ ]t 
  hβ    : ∀ {Γ Δ A} {δ : Sub Γ Δ} {M : Tm Γ (A [ δ ]T)} 
        → head (δ , M) ≡[ ap (Tm _ ∘ _[_]T A) tβ ]≡ M
  Πβ    : ∀ {Γ A B} {M : Tm (Γ , A) B} → app (lam M) ≡ M
  Πη    : ∀ {Γ A B} {M : Tm Γ (Π A B)} → lam (app M) ≡ M
  lam[] : ∀ {Γ Δ A B} {δ : Sub Δ Γ} {M : Tm (Γ , A) B} 
        → (lam M) [ δ ]t ≡[ ap (Tm _) Π[] 
        ]≡ lam (M [ (δ ∘ₛ tail idₛ) , subst (Tm _) [][]T (head idₛ) ]t)
  -- Truncate
  squash : ∀ {T} → is-set (Syntax T)

{-# TERMINATING #-}
_↑_   : ∀ {Γ Δ} → (δ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , A [ δ ]T) (Δ , A)
δ ↑ A = (δ ∘ₛ tail idₛ) , subst (Tm _) [][]T (head idₛ)

squash-Ctx : is-set Ctx
squash-Ctx = squash

squash-Ty  : ∀ {Γ} → is-set (Ty Γ)
squash-Ty  = squash

squash-Tm  : ∀ {Γ A} → is-set (Tm Γ A)
squash-Tm  = squash

squash-Sub : ∀ {Γ Δ} → is-set (Sub Γ Δ)
squash-Sub = squash

Ctx-elim : ∀ {ℓ} (P : Ctx → Type ℓ)
         → (∀ Σ → is-set (P Σ)) → P ε → (∀ {Γ A} → P Γ → P (Γ , A)) 
         → ∀ Γ → P Γ
Ctx-elim _ _ Pε _ ε = Pε
Ctx-elim P Pset Pε PΓA (Γ , A) = PΓA (Ctx-elim P Pset Pε PΓA Γ)
Ctx-elim P Pset Pε PΓA (squash Γ Δ α β i j)
  = is-set→squarep (λ i j → Pset (squash Γ Δ α β i j)) 
    (λ _ → go Γ) (λ i → go (α i)) (λ i → go (β i)) (λ i → go Δ) i j
  where
    go : ∀ Σ → P Σ
    go = Ctx-elim P Pset Pε PΓA

-- Below are two half-finished approaches to defining substitution as a reducing
-- function.
-- The first uses indexed matching that relies on data constructor injectivity,
-- which Cubical Agda does not yet support. This means that it does not compute
-- on transports, which is painful.
-- The second gets around the indexed matching restrictions by being polymorphic
-- over the index and later requiring an equality proof (any index, as long as
-- it is SynTy Δ). The downside is that Agda cannot automatically reject the
-- absurd cases.
--
-- Probably the best thing to do here would be to define an explicit eliminator,
-- but this is a quite painful amount of boilerplate. Perhaps I could create
-- a view of Syntax T which only has constructors associated with Ty...

ty-sub : ∀ {Γ Δ T} → T ≡ SynTy Δ → Syntax T → Sub Γ Δ → Ty Γ
ty-sub p U δ = U
ty-sub p (El M) δ = {!!}
ty-sub p (Π A B) δ = {!   !}
ty-sub p ε _ = absurd (SubTy-disjoint p)
ty-sub p (_ , _) _ = absurd (SubTy-disjoint p)
ty-sub p idₛ δ = absurd (SubTy-disjoint p)
ty-sub p (_ ∘ₛ _) _ = absurd (SubTy-disjoint p)
ty-sub p (tail _) _ = absurd (SubTy-disjoint p)
ty-sub p (lam _) _ = absurd (TmTy-disjoint p)
ty-sub p (app _) _ = absurd (TmTy-disjoint p)
ty-sub p (head _) _ = absurd (TmTy-disjoint p)
ty-sub p (x [ _ ]t) _ = absurd (TmTy-disjoint p)
ty-sub p ([id]T i) δ = {!   !}
ty-sub p ([][]T i) δ = {!   !}
ty-sub p (U[] i) δ = {!   !}
ty-sub p (El[] i) δ = {!   !}
ty-sub p (Π[] i) δ = {!   !}
ty-sub p (idl i) δ = {!   !}
ty-sub p (idr i) δ = {!   !}
ty-sub p (ass i) δ = {!   !}
ty-sub p (,∘ i) δ = {!   !}
ty-sub p (tβ i) δ = {!   !}
ty-sub p (,η i) δ = {!   !}
ty-sub p (εη i) δ = {!   !}
ty-sub p ([id]t i) δ = {!   !}
ty-sub p ([][]t i) δ = {!   !}
ty-sub p (hβ i) δ = {!   !}
ty-sub p (Πβ i) δ = {!   !}
ty-sub p (Πη i) δ = {!   !}
ty-sub p (lam[] i) δ = {!   !}
ty-sub p (squash A A₁ x y i i₁) δ = {!   !}

-- -- Unsupported Indexed Match... Need to use the eliminator
U [ δ ]T = U
El M [ δ ]T = El (M [ δ ]t)
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ↑ A ]T)
-- These are actually reasonably challenging equations to prove...
[id]T i [ δ ]T = {!   !}
[][]T i [ δ ]T = {!   !}
U[] i [ δ ]T = refl {x = U} i
-- If _[_]T computed on paths, the below equation would hold definitionally 
-- true...
El[] {A = A} {δ = σ} i [ δ ]T
  = ap (λ x → El (x [ δ ]t)) 
       (ap (λ x → subst (Tm _) x (A [ σ ]t)) (squash U U (U[] {δ = σ}) refl) 
  ∙ transport-refl (A [ σ ]t)) (~ i)
Π[] {A = A} {B = B} {δ = σ} i [ δ ]T 
  = Π ((A [ σ ]T) [ δ ]T) ((B [ σ ↑ A ]T) [ δ ↑ (A [ σ ]T) ]T)
_[_]T {Γ} {Δ} (squash A B α β i j) δ = {!!}
  -- = is-set→squarep (λ i j → squash {T = SynTy Δ} {!!}) {!!} {!!} {!!} {!!} i j
