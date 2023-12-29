open import 1Lab.Type using (Type)

-- I want to define a normal form syntax where idₛ, tail, ∘ₛ etc all reduce
-- But this runs into the classic problem of the recursion/dependency hell
module DepTyChk.Nf where

infix 5 _∋_
infixl 6 _,_
-- infix 7 _[_]T

data Ctx : Type
data Ty (Γ : Ctx) : Type
data Tm : ∀ Γ → Ty Γ → Type
data Sub : Ctx → Ctx → Type
data _∋_ : ∀ Γ → Ty Γ → Type

data Ctx where
  ε   : Ctx
  _,_ : ∀ Γ → Ty Γ → Ctx

data Ty Γ where
  U  : Ty Γ
  El : Tm Γ U → Ty Γ
  Π  : ∀ A → Ty (Γ , A) → Ty Γ

weak : ∀ {Γ A} → Ty Γ → Ty (Γ , A)

data _∋_ where
  here  : ∀ {Γ} {A : Ty Γ} → Γ , A ∋ weak A
  there : ∀ {Γ} {A B : Ty Γ} → Γ ∋ A → Γ , B ∋ weak A

data Tm where


data Sub where
