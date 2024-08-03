{-# OPTIONS --prop --show-irrelevant --rewriting --local-confluence-check #-}

open import Coincidences.Utils

module Coincidences.Syntax where

data Ctx : Set
data Ty  : Ctx → Set

variable
  Γ Δ θ Ξ : Ctx
  A : Ty Γ
  B : Ty Δ
  C : Ty θ
  D : Ty Ξ

data U : Set
El : U → Set

data U where
  ⊥'  : U
  Π'  : ∀ A → (El A → U) → U

El ⊥' = ⊥
El (Π' A B) = ∀ x → El (B x)

⟦_⟧c : Ctx → Set

SemCtx : Set₁
SemCtx = Set

SemTy : Set → Set
SemTy Γ = Γ → U

data Ctx where
  ε   : Ctx
  _,_ : ∀ Γ → Ty Γ → Ctx

data Tm  : ∀ Γ → SemTy ⟦ Γ ⟧c → Set

data Ty where
  ⊥'  : Ty Γ
  Π'  : ∀ A → Ty (Γ , A) → Ty Γ
  El' : Tm Γ (λ _ → ⊥') → Ty Γ

⟦_⟧T : Ty Γ → SemTy ⟦ Γ ⟧c

εs : SemCtx
εs = ⊤

_,s_ : ∀ Γ → SemTy Γ → SemCtx
Γ ,s A = Σ Γ (El ∘ A)

⟦ ε ⟧c = εs
⟦ Γ , A ⟧c = ⟦ Γ ⟧c ,s ⟦ A ⟧T

Πsem : ∀ {Γ} A → SemTy (Γ ,s A) → SemTy Γ
Πsem A B ρ = Π' (A ρ) (B ∘ (ρ ,_))

SemVal : ∀ Γ → SemTy Γ → Set
SemVal _ A = ∀ ρ → El (A ρ)

⟦_⟧tm : ∀ {Γ A} → Tm Γ A → SemVal ⟦ Γ ⟧c A

⟦ ⊥'     ⟧T _ = ⊥'
⟦ Π' A B ⟧T   = Πsem ⟦ A ⟧T ⟦ B ⟧T
⟦ El' M  ⟧T   = ⊥-elim ∘ ⟦ M ⟧tm

SemSub : SemCtx → SemCtx → Set
SemSub Γ Δ = Γ → Δ

semwk :  ∀ {Γ} A → SemSub (Γ ,s A) Γ
semwk _ = proj₁

semvz : ∀ {Γ A} → SemVal (Γ ,s A) (A ∘ semwk A)
semvz = proj₂

sem<_> : ∀ {Γ A} (M : SemVal Γ A) → SemSub Γ (Γ ,s A)
sem< M > Γ = Γ , M Γ

data Var : ∀ Γ → SemTy ⟦ Γ ⟧c → Set where
  vz : ∀ {Γ A} → Var (Γ , A) (⟦ A ⟧T ∘ semwk ⟦ A ⟧T)
  vs : ∀ {Γ A B} → Var Γ B → Var (Γ , A) (B ∘ semwk ⟦ A ⟧T)

⟦_⟧v : ∀ {Γ A} → Var Γ A → SemVal ⟦ Γ ⟧c A
⟦ vz ⟧v = semvz
⟦ vs x ⟧v (ρ , M) = ⟦ x ⟧v ρ

data Tm where
  var : ∀ {Γ A} → Var Γ A → Tm Γ A
  app : ∀ {Γ A B} → Tm Γ (Πsem A B) → (N : Tm Γ A) → Tm Γ (B ∘ sem< ⟦ N ⟧tm >)
  lam : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Πsem ⟦ A ⟧T B)

appsem : ∀ {Γ A B} → SemVal Γ (Πsem A B) → (N : SemVal Γ A) 
       → SemVal Γ (B ∘ sem< N >)
appsem M N ρ = (M ρ) (N ρ)

lamsem : ∀ {Γ A B} → SemVal (Γ ,s A) B → SemVal Γ (Πsem A B)
lamsem M ρ N = M (ρ , N)

⟦ var x   ⟧tm = ⟦ x ⟧v
⟦ app M N ⟧tm = appsem ⟦ M ⟧tm ⟦ N ⟧tm
⟦ lam M   ⟧tm = lamsem ⟦ M ⟧tm

private module Congruences where
  Ty≡ = cong Ty
  SemTy≡ = cong SemTy
  SemSub≡ = cong₂ SemSub
  ⟦_⟧c≡ = cong ⟦_⟧c 

  Var≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂) 
        → Var Γ₁ A₁ ≡ Var Γ₂ A₂
  Var≡ refl refl = refl

  Tm≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂) 
      → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂
  Tm≡ refl refl = refl

  SemVal≡ :  ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A : A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂) 
          → SemVal Γ₁ A₁ ≡ SemVal Γ₂ A₂
  SemVal≡ refl refl = refl

  ⟦⟧tm≡ : ∀ {Γ₁ Γ₂ A₁ A₂ M₁ M₂} (Γ≡ : Γ₁ ≡ Γ₂) 
            (A≡ : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂)
        → M₁ ≡[ Tm≡ Γ≡ A≡ ]≡ M₂ → ⟦ M₁ ⟧tm ≡[ SemVal≡ ⟦ Γ≡ ⟧c≡ A≡ ]≡ ⟦ M₂ ⟧tm
  ⟦⟧tm≡ refl refl refl = refl

  _,≡_ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
      → (Ctx._,_ Γ₁ A₁) ≡ (Ctx._,_ Γ₂ A₂)
  refl ,≡ refl = refl

  ⟦⟧T≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) → A₁ ≡[ Ty≡ Γ≡ ]≡ A₂ 
        → ⟦ A₁ ⟧T ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ ⟦ A₂ ⟧T
  ⟦⟧T≡ refl refl = refl

  ⊥≡ : ∀ {Γ₁ Γ₂} (Γ≡ : Γ₁ ≡ Γ₂) → ⊥' ≡[ Ty≡ Γ≡ ]≡ ⊥'
  ⊥≡ refl = refl

  Π≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
    → B₁ ≡[ Ty≡ (Γ≡ ,≡ A≡) ]≡ B₂ → Π' A₁ B₁ ≡[ Ty≡ Γ≡ ]≡ Π' A₂ B₂
  Π≡ refl refl refl = refl

  El≡ : ∀ {Γ₁ Γ₂ M₁ M₂} (Γ≡ : Γ₁ ≡ Γ₂)
      → M₁ ≡[ Tm≡ Γ≡ (⟦⟧T≡ Γ≡ (⊥≡ Γ≡)) ]≡ M₂
      → El' M₁ ≡[ Ty≡ Γ≡ ]≡ El' M₂
  El≡ refl refl = refl

  _,s≡_ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) → A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂ 
        → Γ₁ ,s A₁ ≡ Γ₂ ,s A₂
  refl ,s≡ refl = refl 

  Πsem≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂) 
        → B₁ ≡[ SemTy≡ (Γ≡ ,s≡ A≡) ]≡ B₂ 
        → Πsem A₁ B₁ ≡[ SemTy≡ Γ≡ ]≡ Πsem A₂ B₂
  Πsem≡ refl refl refl = refl

  var≡ : ∀ {Γ₁ Γ₂ A₁ A₂ x₁ x₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂)
        → (x₁ ≡[ Var≡ Γ≡ A≡ ]≡ x₂) → var x₁ ≡[ Tm≡ Γ≡ A≡ ]≡ var x₂
  var≡ refl refl refl = refl

  lam≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂ M₁ M₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
            (B≡ : B₁ ≡[ SemTy≡ ⟦ Γ≡ ,≡ A≡ ⟧c≡ ]≡ B₂) 
            (M≡ : M₁ ≡[ Tm≡ (Γ≡ ,≡ A≡) B≡ ]≡ M₂) 
        → lam M₁ ≡[ Tm≡ Γ≡ (Πsem≡ ⟦ Γ≡ ⟧c≡ (⟦⟧T≡ Γ≡ A≡) B≡) ]≡ lam M₂
  lam≡ refl refl refl refl = refl

  semwk≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} (Γ≡ : Γ₁ ≡ Γ₂) 
             (A≡ : A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂) (B≡ : B₁ ≡[ SemTy≡ Γ≡ ]≡ B₂) 
         → B₁ ∘ semwk A₁ ≡[ SemTy≡ (Γ≡ ,s≡ A≡) ]≡ B₂ ∘ semwk A₂ 
  semwk≡ refl refl  refl = refl

  sem<>≡ : ∀ {Γ₁ Γ₂ A₁ A₂ M₁ M₂ B₁ B₂} (Γ≡ : Γ₁ ≡ Γ₂) 
             (A≡ : A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂)
             (M≡ : M₁ ≡[ SemVal≡ Γ≡ A≡ ]≡ M₂) 
             (B≡ : B₁ ≡[ SemTy≡ (Γ≡ ,s≡ A≡) ]≡ B₂)
          → B₁ ∘ sem< M₁ > ≡[ SemTy≡ Γ≡ ]≡ B₂ ∘ sem< M₂ >
  sem<>≡ refl refl refl refl = refl

  app≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂ M₁ M₂ N₁ N₂} (Γ≡ : Γ₁ ≡ Γ₂) 
            (A≡ : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂) 
            (B≡ : B₁ ≡[ SemTy≡ (⟦ Γ≡ ⟧c≡ ,s≡ A≡) ]≡ B₂) 
        → M₁ ≡[ Tm≡ Γ≡ (Πsem≡ ⟦ Γ≡ ⟧c≡ A≡ B≡) ]≡ M₂
        → (N≡ : N₁ ≡[ Tm≡ Γ≡ A≡ ]≡ N₂)
        → app M₁ N₁ ≡[ Tm≡ Γ≡ (sem<>≡ ⟦ Γ≡ ⟧c≡ A≡ (⟦⟧tm≡ Γ≡ A≡ N≡) B≡) 
      ]≡ app M₂ N₂
  app≡ refl refl refl refl refl = refl

  []sem≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
         → A₁ ≡[ SemTy≡ Δ≡ ]≡ A₂ → δ₁ ≡[ SemSub≡ Γ≡ Δ≡ ]≡ δ₂ 
         → A₁ ∘ δ₁ ≡[ SemTy≡ Γ≡ ]≡ A₂ ∘ δ₂
  []sem≡ refl refl refl refl = refl

  vz≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂)
      → vz ≡[ Var≡ (Γ≡ ,≡ A≡) (semwk≡ ⟦ Γ≡ ⟧c≡ (⟦⟧T≡ Γ≡ A≡) (⟦⟧T≡ Γ≡ A≡)) ]≡ vz
  vz≡ refl refl = refl

  vs≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂ x₁ x₂} (Γ≡ : Γ₁ ≡ Γ₂)
          (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) (B≡ : B₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ B₂)
          (x≡ : x₁ ≡[ Var≡ Γ≡ B≡ ]≡ x₂)
      → vs x₁ ≡[ Var≡ (Γ≡ ,≡ A≡) (semwk≡ ⟦ Γ≡ ⟧c≡ (⟦⟧T≡ Γ≡ A≡) B≡) ]≡ vs x₂
  vs≡ refl refl refl refl = refl

  appsem≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂ M₁ M₂ N₁ N₂} (Γ≡ : Γ₁ ≡ Γ₂)
              (A≡ : A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂) (B≡ : B₁ ≡[ SemTy≡ (Γ≡ ,s≡ A≡) ]≡ B₂)
          → M₁ ≡[ SemVal≡ Γ≡ (Πsem≡ Γ≡ A≡ B≡) ]≡ M₂
          → (N≡ : N₁ ≡[ SemVal≡ Γ≡ A≡ ]≡ N₂)
          → appsem M₁ N₁ ≡[ SemVal≡ Γ≡ (sem<>≡ Γ≡ A≡ N≡ B≡) ]≡ appsem M₂ N₂
  appsem≡ refl refl refl refl refl = refl

  lamsem≡ : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂ M₁ M₂} (Γ≡ : Γ₁ ≡ Γ₂)
              (A≡ : A₁ ≡[ SemTy≡ Γ≡ ]≡ A₂) (B≡ : B₁ ≡[ SemTy≡ (Γ≡ ,s≡ A≡) ]≡ B₂)
          → M₁ ≡[ SemVal≡ (Γ≡ ,s≡ A≡) B≡ ]≡ M₂
          → lamsem M₁ ≡[ SemVal≡ Γ≡ (Πsem≡ Γ≡ A≡ B≡) ]≡ lamsem M₂
  lamsem≡ refl refl refl refl = refl

open Congruences public
