{-# OPTIONS --rewriting #-}
--local-confluence-check

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; subst; sym; cong; dcong₂; subst-application′)
  renaming (trans to _∙_)
open import Function using (_∘_; id)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Coincidences.Utils
open import Coincidences.Syntax

module Coincidences.Sub where

infixl 100 _[_]w _[_]s _[_]wv _[_]wtm _[_]sv _[_]stm _[_] _[_]tm _[_]v

data Wk  : Ctx → Ctx → Set
data Sub : Ctx → Ctx → Set
⟦_⟧w : Wk Δ Γ  → ⟦ Δ ⟧c → ⟦ Γ ⟧c 
⟦_⟧s : Sub Δ Γ → ⟦ Δ ⟧c → ⟦ Γ ⟧c
_[_]w  : Ty Γ → Wk Δ Γ  → Ty Δ
_[_]s  : Ty Γ → Sub Δ Γ → Ty Δ
_[_]w≡ : ∀ A (δ : Wk Δ Γ)  → ⟦ A [ δ ]w ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧w
_[_]s≡ : ∀ A (δ : Sub Δ Γ) → ⟦ A [ δ ]s ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧s

-- Prepare for a lot of duplication between weakenings/substitutions. 
-- I don't know how to get rid of this without Agda's termination checker
-- complaining.
data Wk where
  wk : Wk (Γ , A) Γ
  _↑_ : ∀ (δ : Wk Γ Δ) A → Wk (Γ , A [ δ ]w) (Δ , A)

data Sub where
  <_> : Tm Γ ⟦ A ⟧T → Sub Γ (Γ , A)
  _↑_ : ∀ (δ : Sub Γ Δ) A → Sub (Γ , A [ δ ]s) (Δ , A)

⟦ wk ⟧w            = proj₁
⟦ δ ↑ A ⟧w (ρ , M) = ⟦ δ ⟧w ρ , subst (λ AB → El (AB ρ)) (A [ δ ]w≡) M

⟦ < M > ⟧s ρ       = ρ , ⟦ M ⟧tm ρ
⟦ δ ↑ A ⟧s (ρ , M) = ⟦ δ ⟧s ρ , subst (λ AB → El (AB ρ)) (A [ δ ]s≡) M

_[_]wtm  : ∀ {Γ A} → Tm Γ A → (δ : Wk Δ Γ)  → Tm Δ (A ∘ ⟦ δ ⟧w)
_[_]stm  : ∀ {Γ A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧s)

⊥' [ δ ]w = ⊥'
(Π' A B) [ δ ]w = Π' (A [ δ ]w) (B [ δ ↑ A ]w)
El' A [ δ ]w = El' (A [ δ ]wtm) 

⊥' [ δ ]s = ⊥'
Π' A B [ δ ]s = Π' (A [ δ ]s) (B [ δ ↑ A ]s)
El' A [ δ ]s = El' (A [ δ ]stm) 

-- TODO: Simplify these proofs
[]w-helper : ∀ {⟦A[δ]⟧} (B : Ty (Γ , A)) (δ : Wk Δ Γ) 
            (p : ⟦A[δ]⟧ ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧w) 
        → subst (λ A′ → Σ ⟦ Δ ⟧c (El ∘ A′) → U) (sym p)
          (λ where (ρ , x) → ⟦ B ⟧T (⟦ δ ⟧w ρ , x))
        ≡ (λ where (ρ , x) → ⟦ B ⟧T (⟦ δ ⟧w ρ , subst (λ AB → El (AB ρ)) p x))
[]w-helper B δ refl = refl

[]s-helper : ∀ {⟦A[δ]⟧} (B : Ty (Γ , A)) (δ : Sub Δ Γ) 
            (p : ⟦A[δ]⟧ ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧s) 
        → subst (λ A′ → Σ ⟦ Δ ⟧c (El ∘ A′) → U) (sym p)
          (λ where (ρ , x) → ⟦ B ⟧T (⟦ δ ⟧s ρ , x))
        ≡ (λ where (ρ , x) → ⟦ B ⟧T (⟦ δ ⟧s ρ , subst (λ AB → El (AB ρ)) p x))
[]s-helper B δ refl = refl

⊥' [ δ ]w≡ = refl
Π' A B [ δ ]w≡ 
  = cong (Πsem ⟦ A [ δ ]w ⟧T) (B [ δ ↑ A ]w≡)
  ∙ sym (dcong₂ Πsem (sym A≡) ([]w-helper B δ A≡))
  where A≡ = A [ δ ]w≡
El' A [ δ ]w≡ = refl

⊥' [ δ ]s≡ = refl
Π' A B [ δ ]s≡ 
  = cong (Πsem ⟦ A [ δ ]s ⟧T) (B [ δ ↑ A ]s≡)
  ∙ sym (dcong₂ Πsem (sym A≡) ([]s-helper B δ A≡))
  where A≡ = A [ δ ]s≡
El' A [ δ ]s≡ = refl

{-# REWRITE _[_]w≡ _[_]s≡ #-}

_[_]wtm≡ : ∀ {A} (M : Tm Γ A) (δ : Wk Δ Γ) 
         → ⟦ M [ δ ]wtm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧w
_[_]wv : ∀ {A} → Var Γ A → (δ : Wk Δ Γ) → Var Δ (A ∘ ⟦ δ ⟧w)
_[_]wv≡ : ∀ {A} (x : Var Γ A) (δ : Wk Δ Γ) 
        → ⟦ x [ δ ]wv ⟧v ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧w

x    [ wk    ]wv = vs x
vz   [ δ ↑ A ]wv = vz
vs x [ δ ↑ A ]wv = vs (x [ δ ]wv)

x [ wk ]wv≡ = refl
vz [ δ ↑ A ]wv≡ = refl
vs x [ δ ↑ A ]wv≡ = cong (_∘ proj₁) (x [ δ ]wv≡)

var x [ δ ]wtm = var (x [ δ ]wv)
app {B = B} M N [ δ ]wtm 
  = subst (λ x → (Tm _ (λ ρ → B (⟦ δ ⟧w ρ , x ρ)))) 
          (N [ δ ]wtm≡) (app (M [ δ ]wtm) (N [ δ ]wtm))
lam M [ δ ]wtm = lam (M [ δ ↑ _ ]wtm)

var x [ δ ]wtm≡ = x [ δ ]wv≡
app {B = B} M N [ δ ]wtm≡ 
  = sym (subst-application′ _ (λ _ → ⟦_⟧tm) (N [ δ ]wtm≡)) 
  ∙ dcong-app (cong appsem (M [ δ ]wtm≡)) (N [ δ ]wtm≡)
lam M [ δ ]wtm≡ = cong (λ M′ ρ → M′ ∘ (ρ ,_)) (M [ δ ↑ _ ]wtm≡)

{-# REWRITE _[_]wv≡ _[_]wtm≡ #-}

_[_]stm≡ : ∀ {A} (M : Tm Γ A) (δ : Sub Δ Γ) 
         → ⟦ M [ δ ]stm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧s

_[_]sv  : ∀ {A} → Var Γ A → (δ : Sub Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧s)
_[_]sv≡ : ∀ {A} (x : Var Γ A) (δ : Sub Δ Γ) 
       → ⟦ x [ δ ]sv ⟧tm ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧s

var x [ δ ]stm = x [ δ ]sv
app {B = B} M N [ δ ]stm 
  = subst (λ x → (Tm _ (λ ρ → B (⟦ δ ⟧s ρ , x ρ)))) 
          (N [ δ ]stm≡) (app (M [ δ ]stm) (N [ δ ]stm))
lam M [ δ ]stm = lam (M [ δ ↑ _ ]stm)

var x [ δ ]stm≡ = x [ δ ]sv≡
app {B = B} M N [ δ ]stm≡ 
  = sym (subst-application′ _ (λ _ → ⟦_⟧tm) (N [ δ ]stm≡)) 
  ∙ dcong-app (cong appsem (M [ δ ]stm≡)) (N [ δ ]stm≡)
lam M [ δ ]stm≡ = cong (λ M′ ρ → M′ ∘ (ρ ,_)) (M [ δ ↑ _ ]stm≡)

vz   [ < M > ]sv = M
vs x [ < M > ]sv = var x 
vz   [ δ ↑ A ]sv = var vz
vs x [ δ ↑ A ]sv = x [ δ ]sv [ wk ]wtm

vz [ < M > ]sv≡ = refl
vs x [ < M > ]sv≡ = refl
vz [ δ ↑ A ]sv≡ = refl
vs x [ δ ↑ A ]sv≡ = cong (_∘ proj₁) (x [ δ ]sv≡)
 
{-# REWRITE _[_]sv≡ _[_]stm≡ #-}

data MSub : Ctx → Ctx → Set where
  idₛ  : MSub Γ Γ
  _◂w_ : MSub Δ Γ → Wk θ Δ  → MSub θ Γ
  _◂s_ : MSub Δ Γ → Sub θ Δ → MSub θ Γ

_[_] : Ty Γ → MSub Δ Γ → Ty Δ
A [ idₛ ] = A
A [ δ ◂w σ ] = A [ δ ] [ σ ]w
A [ δ ◂s σ ] = A [ δ ] [ σ ]s

_↑m_ : ∀ δ A → MSub (Δ , A [ δ ]) (Γ , A)
idₛ ↑m A = idₛ
(δ ◂w σ) ↑m A = (δ ↑m A) ◂w (σ ↑ (A [ δ ]))
(δ ◂s σ) ↑m A = (δ ↑m A) ◂s (σ ↑ (A [ δ ]))

⟦_⟧ms : MSub Δ Γ → ⟦ Δ ⟧c → ⟦ Γ ⟧c
⟦ idₛ ⟧ms = id
⟦ δ ◂w σ ⟧ms = ⟦ δ ⟧ms ∘ ⟦ σ ⟧w 
⟦ δ ◂s σ ⟧ms = ⟦ δ ⟧ms ∘ ⟦ σ ⟧s

_[_]tm : ∀ {A} → Tm Γ A → ∀ δ → Tm Δ (A ∘ ⟦ δ ⟧ms)
M [ idₛ ]tm = M
M [ δ ◂w σ ]tm = M [ δ ]tm [ σ ]wtm
M [ δ ◂s σ ]tm = M [ δ ]tm [ σ ]stm

_[_]v : ∀ {A} → Var Γ A → ∀ δ → Tm Δ (A ∘ ⟦ δ ⟧ms)
x [ idₛ ]v = var x
x [ δ ◂w σ ]v = (x [ δ ]v) [ σ ]wtm 
x [ δ ◂s σ ]v = (x [ δ ]v) [ σ ]stm

-- All the below proofs are pretty-much identical. Surely we can abstract over
-- this repetition?

_[_]≡ : ∀ A (δ : MSub Δ Γ) → ⟦ A [ δ ] ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧ms 
A [ idₛ ]≡ = refl
A [ δ ◂w σ ]≡ = cong (_∘ ⟦ σ ⟧w) (A [ δ ]≡)  
A [ δ ◂s σ ]≡ = cong (_∘ ⟦ σ ⟧s) (A [ δ ]≡)

_[_]tm≡ : ∀ {A} (M : Tm Γ A) (δ : MSub Δ Γ) → ⟦ M [ δ ]tm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧ms 
M [ idₛ ]tm≡ = refl
M [ δ ◂w σ ]tm≡ = cong (_∘ ⟦ σ ⟧w) (M [ δ ]tm≡)  
M [ δ ◂s σ ]tm≡ = cong (_∘ ⟦ σ ⟧s) (M [ δ ]tm≡) 

_[_]v≡ : ∀ {A} (x : Var Γ A) (δ : MSub Δ Γ) → ⟦ x [ δ ]v ⟧tm ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧ms 
x [ idₛ ]v≡ = refl
x [ δ ◂w σ ]v≡ = cong (_∘ ⟦ σ ⟧w) (x [ δ ]v≡)  
x [ δ ◂s σ ]v≡ = cong (_∘ ⟦ σ ⟧s) (x [ δ ]v≡) 

{-# REWRITE _[_]≡ _[_]tm≡ _[_]v≡ #-}

⊥[] : ∀ (δ : MSub Δ Γ) → ⊥' [ δ ] ≡ ⊥'
⊥[] idₛ = refl
⊥[] (δ ◂w σ) = cong (_[ σ ]w) (⊥[] δ)
⊥[] (δ ◂s σ) = cong (_[ σ ]s) (⊥[] δ)

Π[] : ∀ (δ : MSub Δ Γ) → Π' A B [ δ ] ≡ Π' (A [ δ ]) (B [ δ ↑m A ])
Π[] idₛ = refl
Π[] (δ ◂w σ) = cong (_[ σ ]w) (Π[] δ)
Π[] (δ ◂s σ) = cong (_[ σ ]s) (Π[] δ)

El[] : ∀ {M} (δ : MSub Δ Γ) → El' M [ δ ] ≡ El' (M [ δ ]tm)
El[] idₛ = refl
El[] (δ ◂w σ) = cong (_[ σ ]w) (El[] δ)
El[] (δ ◂s σ) = cong (_[ σ ]s) (El[] δ)

{-# REWRITE ⊥[] Π[] El[] #-}

⟦⟧↑m : (δ : MSub Δ Γ) → ⟦ δ ↑m A ⟧ms ≡ λ where (⟦Γ⟧ , ⟦A⟧) → ⟦ δ ⟧ms ⟦Γ⟧ , ⟦A⟧
⟦⟧↑m idₛ = refl
⟦⟧↑m {A = A} (δ ◂w σ) = cong (_∘ ⟦ σ ↑ A [ δ ] ⟧w) (⟦⟧↑m δ)
⟦⟧↑m {A = A} (δ ◂s σ) = cong (_∘ ⟦ σ ↑ A [ δ ] ⟧s) (⟦⟧↑m δ)

{-# REWRITE ⟦⟧↑m #-}

app[] : ∀ {A B} {M : Tm Γ (Πsem A B)} {N : Tm Γ A} (δ : MSub Δ Γ) 
      → app M N [ δ ]tm ≡ app (M [ δ ]tm) (N [ δ ]tm)
app[] idₛ = refl
app[] (δ ◂w σ) = cong (_[ σ ]wtm) (app[] δ)
app[] (δ ◂s σ) = cong (_[ σ ]stm) (app[] δ)

lam[] : ∀ {A B} {M : Tm (Γ , A) B} (δ : MSub Δ Γ) 
      → lam M [ δ ]tm ≡ lam (M [ δ ↑m _ ]tm)
lam[] idₛ = refl
lam[] (δ ◂w σ) = cong (_[ σ ]wtm) (lam[] δ)
lam[] (δ ◂s σ) = cong (_[ σ ]stm) (lam[] δ)

{-# REWRITE app[] lam[] #-}

_[_]sem : SemTy ⟦ Γ ⟧c → MSub Δ Γ → SemTy ⟦ Δ ⟧c
A [ δ ]sem = A ∘ ⟦ δ ⟧ms

variable
  δ : MSub Δ Γ
  σ : MSub θ Δ
  