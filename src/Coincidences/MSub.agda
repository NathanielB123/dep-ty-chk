{-# OPTIONS --rewriting --prop #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Sub

module Coincidences.MSub where

infixl 100 _[_] _[_]tm _[_]v _[_]tys 

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

⟦_⟧ms : MSub Δ Γ → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c
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

var[] : ∀ {A} {x : Var Γ A} (δ : MSub Δ Γ)
      → var x [ δ ]tm ≡ x [ δ ]v
var[] idₛ = refl
var[] (δ ◂w σ) = cong (_[ σ ]wtm) (var[] δ)
var[] (δ ◂s σ) = cong (_[ σ ]stm) (var[] δ)

app[] : ∀ {A B} {M : Tm Γ (Πsem A B)} {N : Tm Γ A} (δ : MSub Δ Γ) 
      → app M N [ δ ]tm ≡ app (M [ δ ]tm) (N [ δ ]tm)
app[] idₛ = refl
app[] (δ ◂w σ) = [ cong (_[ σ ]wtm) (app[] δ) ]p
app[] (δ ◂s σ) = [ cong (_[ σ ]stm) (app[] δ) ]p

lam[] : ∀ {A B} {M : Tm (Γ , A) B} (δ : MSub Δ Γ) 
      → lam M [ δ ]tm ≡ lam (M [ δ ↑m _ ]tm)
lam[] idₛ = refl
lam[] (δ ◂w σ) = [ cong (_[ σ ]wtm) (lam[] δ) ]p
lam[] (δ ◂s σ) = [ cong (_[ σ ]stm) (lam[] δ) ]p

{-# REWRITE var[] app[] lam[] #-}

_[_]sem : SemTy ⟦ Γ ⟧c → MSub Δ Γ → SemTy ⟦ Δ ⟧c
A [ δ ]sem = A ∘ ⟦ δ ⟧ms

⟨_⟩w : Wk Δ Γ → MSub Δ Γ
⟨ δ ⟩w = idₛ ◂w δ

⟨_⟩s : Sub Δ Γ → MSub Δ Γ
⟨ δ ⟩s = idₛ ◂s δ

-- The lam[] rewrite rule sometimes doesn't apply. I am not sure why - is this
-- an Agda typechecker bug?
-- UPDATE: These sorts of issues only seem to crop up when there is at least
-- rule which fails `--local-confluence-check` so I assume it is to do with
-- confluence: there are multiple possible reductions, and Agda unfortunately
-- doesn't take th one we would like it to

agda-is-broke : ∀ {N B} (M : Tm (Γ , (A [ ⟨ < N > ⟩s ])) B) (δ : MSub Δ Γ)
              → lam M [ δ ]tm ≡ lam (M [ δ ↑m _ ]tm)
agda-is-broke M δ = lam[] {M = M} δ
{-# REWRITE agda-is-broke #-}

_[_]tys : Tys Γ → MSub Δ Γ → Tys Δ
_↑↑_ : ∀ (δ : MSub Δ Γ) Γ′ → MSub (Δ ++ Γ′ [ δ ]tys) (Γ ++ Γ′)

ε        [ δ ]tys = ε
(Γ′ , A) [ δ ]tys = (Γ′ [ δ ]tys) , (A [ δ ↑↑ Γ′ ])
      
δ ↑↑ ε = δ     
δ ↑↑ (Γ′ , A) = (δ ↑↑ Γ′) ↑m A 

⟦[]⟧tys≡ : ∀ Γ′ (δ : MSub Δ Γ) 
         → ⟦ Γ′ [ δ ]tys ⟧tys ≡ ⟦ Γ′ ⟧tys [ ⟦ δ ⟧ms ]semtys

⟦↑↑⟧≡ : ∀ Γ′ (δ : MSub Δ Γ) 
      → ⟦ δ ↑↑ Γ′ ⟧ms ≡[ SemSub≡ (refl ++s≡ (⟦[]⟧tys≡ Γ′ δ)) refl 
     ]≡ ⟦ δ ⟧ms ↑↑sem ⟦ Γ′ ⟧tys

⟦[]⟧tys≡ ε δ = refl
⟦[]⟧tys≡ (Γ′ , A) δ 
  = ,semtys≡ refl δ≡ ([]sem≡ (refl ++s≡ δ≡) refl (erefl ⟦ A ⟧T) (⟦↑↑⟧≡ Γ′ δ))
  where δ≡ = ⟦[]⟧tys≡ Γ′ δ

⟦↑↑⟧≡ ε δ = refl
⟦↑↑⟧≡ (Γ′ , A) δ = ↑s≡ (refl ++s≡ ⟦[]⟧tys≡ Γ′ δ) (⟦↑↑⟧≡ Γ′ δ)

{-# REWRITE ⟦[]⟧tys≡ #-}
{-# REWRITE ⟦↑↑⟧≡  #-}

variable
  δ : MSub Δ Γ
  σ : MSub θ Δ