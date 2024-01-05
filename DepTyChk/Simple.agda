-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

open import 1Lab.Path using 
  (_≡_; subst; ap; refl; transport-refl; _∙_; ~_; coe0→1; _∨_; _∧_; Path
  ; transport; i0; i1; sym; PathP; ap₂; _∙P_; apd; PathP≡Path⁻; PathP≡Path
  ; transport-filler
  )
open import 1Lab.Path.Cartesian using (I-interp)
open import 1Lab.Type using (Type; lsuc; _⊔_; _$_; ¬_; absurd; ⊤; ⊥; tt; _∘_)
open import 1Lab.HLevel using (is-set; is-set→squarep)
open import Data.Dec using (Discrete; Dec; yes; no)
open import 1Lab.Path.IdentitySystem using (set-identity-system)
open import Data.Id.Base using (_≡ᵢ_; reflᵢ; Id-identity-system)
open import Data.Maybe 
  using (Maybe; just; nothing; Map-Maybe; Idiom-Maybe; Bind-Maybe)
open import Meta.Idiom using (Map; Idiom; _<$>_)
open import Meta.Bind using (Bind)
open import Data.Nat renaming (Nat to ℕ)
open Map Map-Maybe
open Idiom Idiom-Maybe
open Bind Bind-Maybe

open import DepTyChk.CubicalUtils using 
  (_≡[_]≡_; coe; map-idx; ∙refl; funky-ap; inl; inr; swap; USum
  ; subst-application
  )

-- A simpler syntax avoiding using cubical features, instead postulating the
-- ways substitutions commute.
-- Once I get this working, I will try and transfer the results vz to a
-- quotiented syntax (where the ways substitutions can be commuted comes from 
-- explicit path constructions)
module DepTyChk.Simple where

infix 5 _∋_
infix 5 _≡T?_
infixl 6 _,_
infixr 7 _[_]T

data Ctx : Type
data Ty : Ctx → Type
data Sub : Ctx → Ctx → Type
data Tm : (Γ : Ctx) → Ty Γ → Type

{-# NO_POSITIVITY_CHECK #-}
data Ctx where
  ε      : Ctx
  _,_    : (Γ : Ctx) → Ty Γ → Ctx

weaken : ∀ {Γ A} → Ty Γ → Ty (Γ , A)
_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
{-# TERMINATING #-}
_[_]t : ∀ {Γ Δ A} → Tm Δ A → (δ : Sub Γ Δ) → Tm Γ (A [ δ ]T)

data Ty where
  U     : ∀ {Γ} → Ty Γ
  El    : ∀ {Γ} → Tm Γ U → Ty Γ
  Π     : ∀ {Γ} → (A : Ty Γ) → Ty (Γ , A) → Ty Γ

data _∋_ : (Γ : Ctx) → Ty Γ → Type where
  vz : ∀ {Γ A} → Γ , A ∋ weaken A 
  vs : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ weaken A

data Tm where
  lam : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
  -- app : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ , A) B
  var : ∀ {Γ A}   → Γ ∋ A → Tm Γ A

data Sub where
  wk  : ∀ {Γ A} → Sub (Γ , A) Γ
  <_> : ∀ {Γ A} → (M : Tm Γ A) → Sub Γ (Γ , A)
  _↑_ : ∀ {Γ Δ} → (δ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , A [ δ ]T) (Δ , A)

squash-Ty : ∀ {Γ} {A B : Ty Γ} (α β : A ≡ B) → α ≡ β
squash-Ty = {!!}

squash-Sub : ∀ {Γ Δ} {δ σ : Sub Γ Δ} (α β : δ ≡ σ) → α ≡ β
squash-Sub = {!!}

weaken A = A [ wk ]T 

-- We postulate the ways we can commute substitutions
-- Ideally we would ensure these equations are satisfied by using a quotient
-- type, but I first just want to get something that works
postulate
  wk<>T : ∀ {Γ B} A {M : Tm Γ B}
        → A [ wk ]T [ < M > ]T ≡ A
  wk↑T  : ∀ {Γ Δ B} A (δ : Sub Γ Δ) 
        → A [ wk ]T [ δ ↑ B ]T ≡ A [ δ ]T [ wk ]T
-- postulate
--   wk<>    : ∀ {Γ Δ A B} M {N : Tm Δ A} (δ : Sub Γ Δ) 
--           → M [ wk ]t [ < N > ]t ≡[ ap (Tm Δ) (wk<>T B δ) ]≡ M
--   wk↑     : ∀ {Γ Δ A B} M (δ : Sub Γ Δ) 
--           → M [ wk ]t [ δ ↑ A ]t ≡[ ap (Tm _) (wk↑T B δ) ]≡ M [ δ ]t [ wk ]t

U [ δ ]T = U
El M [ δ ]T = El (M [ δ ]t)
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ↑ A ]T)

lam M [ δ ]t = lam (M [ δ ↑ _ ]t)
var x [ wk ]t = var (vs x)
var vz [ < N > ]t = subst (Tm _) (sym (wk<>T _)) N
var (vs x) [ < N > ]t = subst (Tm _) (sym (wk<>T _)) (var x)
var vz [ δ ↑ A ]t = subst (Tm _) (sym (wk↑T _ δ)) (var vz)
-- Termination vz is not obvious, but I think this does actually terminate
-- If we split Sub into weakenings and substitutions (as in the base Sub is a
-- wk or < N > respectively), I think it becomes more clear.
-- If δ is a weakening, then both the variable and the substitution will get
-- structurally smaller on every recursive call, eventually producing a variable
-- and the final weakening will just insert a vs constructor without any
-- recursive calls.
-- If δ is a substitution, then we will structurally recurse on the 
-- substitution until we finally hit a < N >, and possibly substitute the term.
-- Then we perform a weakening. Note if the substituted term is now lambda, we
-- might apply some ↑s to the weakening, and seemingly hit this case again, but
-- now δ is a weakening, not a substitution!
var (vs x) [ δ ↑ A ]t = subst (Tm _) (sym (wk↑T _ δ)) (var x [ δ ]t [ wk ]t)

-- Typechecker
-- Todo: Swap "Maybe"s for "Dec"s

is-vz : ∀ {Γ A B} (p : weaken A ≡ B) (x : Γ , A ∋ B) 
        → Maybe (vz ≡[ ap (_ ∋_) p ]≡ x)
is-vz {Γ} {A} {B} p vz 
  = just $ subst (λ x → _ ≡[ ap (_ ∋_) x ]≡ _) (squash-Ty refl p) refl
is-vz p (vs _) = nothing

_≡v?_ : ∀ {Γ A} (x y : Γ ∋ A) → Maybe (x ≡ y)
vz ≡v? y = is-vz refl y
vs x ≡v? y = {!   !}

_≡t?_ : ∀ {Γ A} (M N : Tm Γ A) → Maybe (M ≡ N)
lam M ≡t? lam N = map (ap lam) (M ≡t? N)
lam M ≡t? var _ = nothing
var x ≡t? var y = map (ap var) (x ≡v? y)
var x ≡t? lam _ = nothing  

_≡T?_ : ∀ {Γ} (A B : Ty Γ) → Maybe (A ≡ B)
_≡[_]≡T?_ : ∀ {Γ Δ} (A : Ty Γ) (p : Γ ≡ Δ) (B : Ty Δ) 
          → Maybe (A ≡[ ap Ty p ]≡ B)

U ≡T? U = just refl
U ≡T? El _ = nothing
U ≡T? Π _ _ = nothing
El A ≡T? U = nothing
El A ≡T? El B = map (ap El) (A ≡t? B) 
El A ≡T? Π B C = nothing
Π A B ≡T? U = nothing 
Π A B ≡T? El C = nothing
Π A B ≡T? Π C D = do
  AC ← A ≡T? C
  BD ← B ≡[ ap (_ ,_) AC ]≡T? D
  pure $ ap₂ Π AC BD

A ≡[ p ]≡T? B = subst Maybe (sym (PathP≡Path _ _ _)) (subst Ty p A ≡T? B)

-- Pre-syntax
data UTm : Type where
  lam : UTm → UTm
  var : ℕ → UTm

data UTy : Type where
  U  : UTy
  El : UTm → UTy
  Π  : UTy → UTy → UTy

-- A strengthening (removing a variable from the context)
data Str : Ctx → Ctx → Type
-- Proof that a type is strengthen-able
-- (Semantically, that the variable being removed from the context does not
-- occur in the type/term)
data v∉T {Γ Δ : Ctx} (δ : Str Δ Γ) : Ty Γ → Type
data v∉t {Γ Δ : Ctx} (δ : Str Δ Γ) : ∀ {A} → v∉T δ A → Tm Γ A → Type
data v∉v : ∀ {Γ Δ : Ctx} (δ : Str Δ Γ) {A} → v∉T δ A → Γ ∋ A → Type

strengthenTy : ∀ {Γ Δ} {A : Ty Γ} {δ : Str Δ Γ} → v∉T δ A → Ty Δ

data Str where
  str : ∀ {Γ A} → Str Γ (Γ , A)
  _↑_ : ∀ {Γ Δ} (δ : Str Γ Δ) {A : Ty Δ} (A' : v∉T δ A) 
      → Str (Γ , strengthenTy A') (Δ , A)

data v∉T {Γ} {Δ} δ where
  U  : v∉T δ U
  El : ∀ {M} → v∉t δ U M → v∉T δ (El M)
  Π  : ∀ {A B} (A' : v∉T δ A) → v∉T (δ ↑ A') B → v∉T δ (Π A B)

data v∉t {Γ} {Δ} δ where
  lam : ∀ {A B A' B'} {M : Tm (Γ , A) B}
      → v∉t (δ ↑ A') B' M → v∉t δ (Π A' B') (lam M) 
  var : ∀ {A A'} {x : Γ ∋ A} → v∉v δ A' x → v∉t δ A' (var x)

-- Weaken a proof that a strengthening is valid
weakenStrengthen : ∀ {Γ Δ} {δ : Str Δ Γ} {A} (A' : v∉T δ A) 
                 → v∉T (δ ↑ A') (weaken A)
weakenStrengthen = {!!}

{-# TERMINATING #-}
str-wk : ∀ {Γ Δ} {δ : Str Δ Γ} {A} {A' : v∉T δ A} 
       → strengthenTy (weakenStrengthen A') ≡ weaken (strengthenTy A')
str-wk = {!!}

data v∉v where
  str : ∀ {Γ} {A} {A' : v∉T {Γ = Γ , A} str (weaken A)} {x} 
      → v∉v str A' (vs x)
  vz  : ∀ {Γ Δ} {δ : Str Γ Δ} {A} {A' : v∉T δ A}
      → v∉v (δ ↑ A') (weakenStrengthen A') vz
  vs : ∀ {Γ Δ} {δ : Str Γ Δ} {A} {A' : v∉T δ A} {x}
     → v∉v δ A' x → v∉v (δ ↑ A') (weakenStrengthen A') (vs x)

strengthenTm : ∀ {Γ Δ} {δ : Str Δ Γ} {A} {A' : v∉T δ A} {M} → v∉t δ A' M 
             → Tm Δ (strengthenTy A')
strengthenVar : ∀ {Γ Δ} (δ : Str Δ Γ) {A} {A' : v∉T δ A} x → v∉v δ A' x
             → Δ ∋ strengthenTy A'

strengthenTy U = U
strengthenTy (El A) = El (strengthenTm A)
strengthenTy (Π A B) = Π (strengthenTy A) (strengthenTy B)

strengthenTm (lam M) = lam (strengthenTm M)
strengthenTm (var x) = var (strengthenVar _ _ x)

strengthenVar str (vs x) str = {!!}
strengthenVar (δ ↑ A) vz vz = {!!}
strengthenVar (δ ↑ A) (vs x) (vs x') 
  = subst (_ ∋_) (sym str-wk) (vs (strengthenVar _ _ x'))



checkVar : ∀ Γ (A : Ty Γ) → ℕ → Maybe (Γ ∋ A)
checkVar ε A x = nothing
checkVar (Γ , A) B zero = map (λ p → subst (_ ∋_) p vz) (A [ wk ]T ≡T? B)
checkVar (Γ , A) B (suc x) = do -- = map {!vs!} {! checkVar Γ (B [ _ ]T) x!}
  v ← checkVar Γ {!B!} x
  pure {!!}


checkTm : ∀ {Γ} (A : Ty Γ) → UTm → Maybe (Tm Γ A)
checkTm U (lam M) = nothing
checkTm (El A) (lam M) = nothing 
checkTm (Π A B) (lam M) = map lam (checkTm B M)
checkTm A (var x) = {!!}