open import 1Lab.Type using (Type; _∘_)
open import 1Lab.Path 
  using (_≡_; refl; subst; sym; PathP; ap; apd; ap₂; i0; i1; _∙_; _∙P_)

open import DepTyChk.CubicalUtils 
  using (_≡[_]≡_; apd₂; eq-left; eq-right; _∙[]_)

module DepTyChk.ExplicitSub.Syntax where

infixl 6 _,_

data Ctx : Type
data Ty : Ctx → Type
data Tm : (Γ : Ctx) → Ty Γ → Type

data Ctx where
  ε   : Ctx
  _,_ : (Γ : Ctx) → Ty Γ → Ctx

data Ty where
  U  : ∀ {Γ} → Ty Γ
  El : ∀ {Γ} → Tm Γ U → Ty Γ
  Π  : ∀ {Γ} (A : Ty Γ) → Ty (Γ , A) → Ty Γ

data Sub : Ctx → Ctx → Type

_[_]T : ∀ {Γ Δ} → Ty Γ → Sub Δ Γ → Ty Δ

data Sub where
  wk  : ∀ {Γ A} → Sub (Γ , A) Γ
  <_> : ∀ {Γ A} → Tm Γ A → Sub Γ (Γ , A)
  _↑_ : ∀ {Γ Δ} (δ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , A [ δ ]T) (Δ , A)

data CtxInCtx (Γ : Ctx) : Type

collapse : ∀ Γ → CtxInCtx Γ → Ctx

data CtxInCtx Γ where
  ε   : CtxInCtx Γ
  _,_ : (Δ : CtxInCtx Γ) → Ty (collapse Γ Δ) → CtxInCtx Γ

collapse Γ ε = Γ
collapse Γ (Δ , A) = collapse Γ Δ , A

_[_]C :  ∀ {Γ Δ} → CtxInCtx Γ → Sub Δ Γ → CtxInCtx Δ

_↑↑_ : ∀ {Γ Δ} (δ : Sub Γ Δ) (Σ : CtxInCtx Δ) 
     → Sub (collapse Γ (Σ [ δ ]C)) (collapse Δ Σ) 

ε [ δ ]C = ε
(Σ , A) [ δ ]C = Σ [ δ ]C , A [ δ ↑↑ Σ ]T

δ ↑↑ ε = δ
δ ↑↑ (Σ , A) = (δ ↑↑ Σ) ↑ A

wk<>C : ∀ {Γ B} {M : Tm Γ B} (Δ : CtxInCtx Γ) → Δ [ wk ]C [ < M > ]C ≡ Δ

wk<>↑↑T : ∀ {Γ B} {M : Tm Γ B} {Σ} (A : Ty (collapse Γ Σ)) 
        → A [ wk ↑↑ Σ ]T [ < M > ↑↑ (Σ [ wk ]C) ]T 
       ≡[ ap (Ty ∘ collapse Γ) (wk<>C Σ) 
       ]≡ A

wk↑C : ∀ {Γ Δ A} (δ : Sub Δ Γ) (Σ : CtxInCtx Γ)
     → Σ [ wk ]C [ δ ↑ A ]C ≡ Σ [ δ ]C [ wk ]C

wk↑↑T : ∀ {Γ Δ B} {Σ} (δ : Sub Δ Γ) (A : Ty (collapse Γ Σ)) 
      → (A [ wk ↑↑ Σ ]T [ (δ ↑ B) ↑↑ (Σ [ wk ]C) ]T) 
     ≡[ ap (Ty ∘ collapse _) (wk↑C δ _)
     ]≡ (A [ δ ↑↑ Σ ]T [ wk ↑↑ (Σ [ δ ]C) ]T)

-- We need the definitional reduction rules of _[_]T for some of the equations
-- to typecheck, so we forward declare some term constructors
_[_]t-fwd : ∀ {Γ Δ A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T)
vz-fwd : ∀ {Γ A} → Tm (Γ , A) (A [ wk ]T)

U [ δ ]T = U
El M [ δ ]T = El (M [ δ ]t-fwd)
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ↑ A ]T)

wk<>C ε = refl
wk<>C {M = M} (Δ , A) 
  = apd₂ {B = λ _ → Ty ∘ collapse _} (λ _ → _,_) (wk<>C Δ) (wk<>↑↑T {M = M} A)

wk<vz>C : ∀ {Γ B} (Δ : CtxInCtx (Γ , B)) 
        → Δ [ wk ↑ B ]C [ < vz-fwd > ]C ≡ Δ

wk<vz>↑↑T : ∀ {Γ B} {Δ : CtxInCtx _} (A : Ty (collapse (Γ , B) Δ))
        → A [ (wk ↑ B) ↑↑ Δ ]T [ < vz-fwd > ↑↑ (Δ [ wk ↑ B ]C) ]T 
       ≡[ ap (Ty ∘ collapse (Γ , B)) (wk<vz>C Δ) 
       ]≡ A

<>↑C : ∀ {Γ Δ B M} (δ : Sub Δ Γ) (Σ : CtxInCtx (Γ , B)) 
     → Σ [ δ ↑ B ]C [ < M [ δ ]t-fwd > ]C ≡ Σ [ < M > ]C [ δ ]C

<>↑↑T : ∀ {Γ Δ B M Σ} (δ : Sub Δ Γ) (A : Ty (collapse (Γ , B) Σ)) 
     → A [ (δ ↑ B) ↑↑ Σ ]T [ < M [ δ ]t-fwd > ↑↑ (Σ [ δ ↑ B ]C) ]T 
    ≡[ ap (Ty ∘ collapse Δ) (<>↑C δ Σ)
    ]≡ A [ < M > ↑↑ Σ ]T [ δ ↑↑ (Σ [ < M > ]C) ]T

data Tm where
  lam   : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
  app   : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ , A) B
  vz    : ∀ {Γ A} → Tm (Γ , A) (A [ wk ]T)
  _[_]t : ∀ {Γ Δ A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T)
  
  wk<>↑↑t : ∀ {Γ B} {N : Tm Γ B} {Σ} {A} (M : Tm (collapse Γ Σ) A) 
          → M [ wk ↑↑ Σ ]t [ < N > ↑↑ (Σ [ wk ]C) ]t 
         ≡[ ap₂ Tm (ap (collapse Γ) (wk<>C Σ)) (wk<>↑↑T A) 
         ]≡ M
  wk↑↑t   : ∀ {Γ Δ B} {Σ} {A} (δ : Sub Δ Γ) (M : Tm (collapse Γ Σ) A) 
          → (M [ wk ↑↑ Σ ]t [ (δ ↑ B) ↑↑ (Σ [ wk ]C) ]t) 
         ≡[ ap₂ Tm (ap (collapse _) (wk↑C δ _)) (wk↑↑T δ A)
         ]≡ (M [ δ ↑↑ Σ ]t [ wk ↑↑ (Σ [ δ ]C) ]t)
  lam[]t  : ∀ {Γ Δ B A} (δ : Sub Δ Γ) (M : Tm (Γ , B) A) 
          → lam (M [ δ ↑ B ]t) ≡ lam M [ δ ]t
  vz[<>]t : ∀ {Γ A} (M : Tm Γ A) 
          → vz [ < M > ]t ≡[ ap (Tm Γ) (wk<>↑↑T {Σ = ε} A) ]≡ M
  vz[↑]t  : ∀ {Γ Δ A} (δ : Sub Δ Γ)
          → vz [ δ ↑ A ]t ≡[ apd (λ _ → Tm _) (wk↑↑T {Σ = ε} δ A) ]≡ vz
  β       : ∀ {Γ A B} (M : Tm (Γ , A) B) → app (lam M) ≡ M
  η       : ∀ {Γ A B} (M : Tm Γ (Π A B)) → lam (app M) ≡ M
  wk<vz>↑↑t : ∀ {Γ B Δ A} (M : Tm (collapse (Γ , B) Δ) A) 
            → M [ (wk ↑ B) ↑↑ Δ ]t [ < vz-fwd > ↑↑ (Δ [ wk ↑ B ]C) ]t 
           ≡[ apd₂ (λ _ → Tm) (ap (collapse (Γ , B)) (wk<vz>C Δ)) (wk<vz>↑↑T A)
           ]≡ M 
  <>↑↑t : ∀ {Γ Δ B N Σ A} (δ : Sub Δ Γ) (M : Tm (collapse (Γ , B) Σ) A) 
     → M [ (δ ↑ B) ↑↑ Σ ]t [ < N [ δ ]t-fwd > ↑↑ (Σ [ δ ↑ B ]C) ]t 
    ≡[ apd₂ (λ _ → Tm) (ap (collapse Δ) (<>↑C δ Σ)) (<>↑↑T δ A)
    ]≡ M [ < N > ↑↑ Σ ]t [ δ ↑↑ (Σ [ < N > ]C) ]t

app[]t : ∀ {Γ Δ A B} (δ : Sub Δ Γ) (M : Tm Γ (Π A B)) 
         → app M [ δ ↑ A ]t ≡ app (M [ δ ]t)
app[]t δ M 
  = sym (β (app M [ δ ↑ _ ]t)) ∙ ap app (lam[]t δ _) ∙ ap (app ∘ _[ δ ]t) (η M)

_[_]t-fwd = _[_]t
vz-fwd = vz

wk↑C δ ε = refl
wk↑C δ (Δ , B) 
  = apd₂ {B = λ _ → Ty ∘ collapse _} (λ _ → _,_) (wk↑C δ Δ) (wk↑↑T δ B)

wk<vz>C ε = refl
wk<vz>C (Γ , A) 
  = apd₂ {B = λ _ → Ty ∘ collapse _} (λ _ → _,_) (wk<vz>C Γ) (wk<vz>↑↑T A)

<>↑C δ ε = refl
<>↑C δ (Σ , A) 
  = apd₂ {B = λ _ → Ty ∘ collapse _} (λ _ → _,_) (<>↑C δ Σ) (<>↑↑T δ A)

{-# TERMINATING #-}
wk<>↑↑T U i = U
wk<>↑↑T (El M) = apd (λ _ → El) (wk<>↑↑t M)
wk<>↑↑T (Π A B) = apd₂ (λ _ → Π) (wk<>↑↑T A) (wk<>↑↑T B)

wk↑↑T δ U i = U
wk↑↑T δ (El M) = apd (λ _ → El) (wk↑↑t δ M)
wk↑↑T {Σ = Σ} δ (Π A B) = apd₂ (λ _ → Π) (wk↑↑T δ A) (wk↑↑T δ B)

wk<vz>↑↑T U i = U
wk<vz>↑↑T (El M) = apd (λ _ → El) (wk<vz>↑↑t M)
wk<vz>↑↑T (Π A B) = apd₂ (λ _ → Π) (wk<vz>↑↑T A) (wk<vz>↑↑T B)

<>↑↑T δ U i = U
<>↑↑T δ (El M) = apd (λ _ → El) (<>↑↑t δ M)
<>↑↑T {Σ = Σ} δ (Π A B) = apd₂ (λ _ → Π) (<>↑↑T δ A) (<>↑↑T δ B)

-- Weaken a bunch of times
mwk-T : ∀ {Γ} (Δ : CtxInCtx Γ) → Ty Γ → Ty (collapse Γ Δ)
mwk-T ε A = A
mwk-T (Δ , _) A = mwk-T Δ A [ wk ]T

mwk-t : ∀ {Γ A} (Δ : CtxInCtx Γ) → Tm Γ A → Tm (collapse Γ Δ) (mwk-T Δ A)
mwk-t ε M = M
mwk-t (Δ , _) M = mwk-t Δ M [ wk ]t

-- Base cases (for better type inference)

wk<>T : ∀ {Γ B} {M : Tm Γ B} (A : Ty Γ) → A [ wk ]T [ < M > ]T ≡ A
wk<>T = wk<>↑↑T

wk<>t  : ∀ {Γ A B} {N : Tm Γ B} (M : Tm Γ A) 
       → M [ wk ]t [ < N > ]t ≡[ ap (Tm Γ) (wk<>T A) ]≡ M
wk<>t = wk<>↑↑t

wk<vz>T : ∀ {Γ B} (A : Ty (Γ , B)) 
        → A [ wk ↑ B ]T [ < vz > ]T ≡ A
wk<vz>T = wk<vz>↑↑T

wk↑T : ∀ {Γ Δ B} (δ : Sub Δ Γ) (A : Ty Γ) 
      → A [ wk ]T [ δ ↑ B ]T ≡ A [ δ ]T [ wk ]T
wk↑T = wk↑↑T

wk↑t : ∀ {Γ Δ B A} (δ : Sub Δ Γ) (M : Tm Γ A) 
      → M [ wk ]t [ δ ↑ B ]t ≡[ ap (Tm _) (wk↑T δ A) ]≡ M [ δ ]t [ wk ]t
wk↑t = wk↑↑t

<>↑T : ∀ {Γ Δ B M} (δ : Sub Δ Γ) (A : Ty (Γ , B)) 
     → A [ δ ↑ B ]T [ < M [ δ ]t > ]T ≡ A [ < M > ]T [ δ ]T
<>↑T = <>↑↑T

<>↑t : ∀ {Γ Δ B N A} (δ : Sub Δ Γ) (M : Tm (Γ , B) A) 
     → M [ δ ↑ B ]t [ < N [ δ ]t > ]t 
    ≡[ ap (Tm _) (<>↑T δ A) 
    ]≡ M [ < N > ]t [ δ ]t
<>↑t = <>↑↑t

wk<vz>t : ∀ {Γ B A} (M : Tm (Γ , B) A) 
        → M [ wk ↑ B ]t [ < vz > ]t ≡[ ap (Tm _) (wk<vz>T A) ]≡ M 
wk<vz>t = wk<vz>↑↑t

wk<vz>t′ : ∀ {Γ A B} (M : Tm Γ (Π A B)) 
         → app (M [ wk ]t) [ < vz > ]t ≡[ ap (Tm _) (wk<vz>T B) ]≡ app M
wk<vz>t′ M = sym (ap (_[ < vz > ]t) (app[]t wk M)) ∙[] wk<vz>t (app M)
