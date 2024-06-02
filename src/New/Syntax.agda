-- {-# OPTIONS --overlapping-instances #-}

{-# OPTIONS --without-K #-}
open import Data.Unit using (⊤; tt)
open import Data.Product using (∃; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong)
open import Function.Base using (_∘_; id)


-- I think this file mostly follows a good design, but I want to use Prop and
-- tweak the design of Coed


module New.Syntax where

infix 3 _≈C_
infix 3 _≈s′_
infix 30 _[_]

data Ctx  : Set
data Ty   (Γ : Ctx) : Set
data Sub′ : Ctx → Ctx → Set
data Var′ : (Γ : Ctx) → Ty Γ → Set
data Tm′  : (Γ : Ctx) → Ty Γ → Set
Sub : Ctx → Ctx → Set
Tm : (Γ : Ctx) → Ty Γ → Set

data _≈C_  : Ctx → Ctx → Set
data _≋t′_  : ∀ {Γ₁ Γ₂ A₁ A₂} → Tm′ Γ₁ A₁ → Tm′ Γ₂ A₂ → Set
data _≋T_  : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Set
_≈T_  : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Set
data _≈s′_  : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Sub′ Γ₁ Δ₁ → Sub′ Γ₂ Δ₂ → Set
_≈s_  : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Sub Γ₁ Δ₁ → Sub Γ₂ Δ₂ → Set
_≈t_  : ∀ {Γ₁ Γ₂ A₁ A₂} → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Set

module RelationUtils where
  infix 10 _¹
  infix 10 _⁻¹
  infix 6 _◂_

  data SynUCon : Set
  SynUArg : SynUCon → Set

  data SynUCon where
    ctx ty tm sub : SynUCon
    coed : (C : SynUCon) → SynUCon

  inter : ∀ {C} → SynUArg C → Set

  idx-rel : ∀ C → SynUArg C → SynUArg C → Set

  record Coed C (R : SynUArg C → SynUArg C → Set) (A : SynUArg C) : Set where
    constructor coe
    inductive
    eta-equality
    field
      {B} : SynUArg C
      p : R B A
      raw : inter B

  -- Wrapper to keep SynUArg injective
  record CoedIdx (A : Set) : Set where
    constructor wrap
    inductive
    eta-equality
    field
      wrapped : A

  SynUArg ctx        = ⊤
  SynUArg ty         = Ctx
  SynUArg tm         = ∃ Ty
  SynUArg sub        = Ctx × Ctx
  SynUArg (coed C)   = CoedIdx (SynUArg C)

  inter {ctx}  _          = Ctx
  inter {ty}   Γ          = Ty Γ
  inter {tm}   (Γ , A)    = Tm′ Γ A
  inter {sub}  (Γ , Δ)    = Sub′ Γ Δ
  inter {coed C} (wrap A) = Coed C (idx-rel C) A

  idx-rel ctx                        = _≡_
  idx-rel ty                         = _≈C_
  idx-rel tm  (_ , A₁) (_ , A₂)      = A₁ ≈T A₂
  idx-rel sub (Γ₁ , Δ₁) (Γ₂ , Δ₂)    = (Γ₁ ≈C Γ₂) × (Δ₁ ≈C Δ₂)
  idx-rel (coed C) (wrap x) (wrap y) = idx-rel C x y

  Rel : SynUCon → Set₁
  Rel C = ∀ {A B : SynUArg C} → inter A → inter B → Set

  Pred : SynUCon → Set₁
  Pred C = ∀ {A : SynUArg C} → inter A → Set

  record Eq {C} (R : Rel C) : Set where
    constructor ⟨_,_,_⟩ 
    infixr 5 _∙_
    field
      rfl : ∀ {A} {x : inter A} → R x x
      sym : ∀ {A B} {x : inter A} {y : inter B} → R x y → R y x
      _∙_ : ∀ {A B C} {x : inter A} {y : inter B} {z : inter C} 
          → R x y → R y z → R x z

  open Eq ⦃...⦄ public

  data SymClosure {C} (R : Rel C) : Rel C where
    _¹  : ∀ {A B} {x : inter A} {y : inter B}
        → R x y → SymClosure R x y
    _⁻¹ : ∀ {A B} {x : inter A} {y : inter B}
        → R x y → SymClosure R y x

  data *Closure {C} (R : Rel C) : Rel C where
    rfl* : ∀ {A} {x : inter A} → *Closure R x x
    _◂_  : ∀ {A B C} {x : inter A} {y : inter B} {z : inter C}
         → R x y → *Closure R y z → *Closure R x z

  *SymClosure : ∀ {C} → Rel C → Rel C
  *SymClosure r = *Closure (SymClosure r)

  ⟪_⟫ : ∀ {C} {R : Rel C} {A B} {x : inter A} {y : inter B} 
      → SymClosure R x y → *SymClosure R x y 
  ⟪ p ⟫ = p ◂ rfl*

  ⟪_¹⟫ : ∀ {C} {R : Rel C} {A B} {x : inter A} {y : inter B} 
       → R x y → *SymClosure R x y
  ⟪ p ¹⟫ = ⟪ p ¹ ⟫ 

  ⟪_⁻¹⟫ : ∀ {C} {R : Rel C} {A B} {x : inter A} {y : inter B} 
        → R x y → *SymClosure R y x
  ⟪ p ⁻¹⟫ = ⟪ p ⁻¹ ⟫

  symsym : ∀ {C} {R : Rel C} {A B} {x y}
      → SymClosure R {A} {B} x y
      → SymClosure R {B} {A} y x
  symsym (p  ¹) = p ⁻¹
  symsym (p ⁻¹) = p  ¹

  data Cohd {C IR A₁ A₂} (R : Rel C) : Coed C IR A₁ → Coed C IR A₂ → Set where
    coh : ∀ {A B} {x : inter A} {y : inter B} p q 
        → R x y → Cohd R (coe p x) (coe q y)

  _∙*_ : ∀ {C} {R : Rel C} {A B C} {x : inter A} {y : inter B} {z : inter C}
       → *SymClosure R x y → *SymClosure R y z → *SymClosure R x z
  rfl* ∙* r = r
  (p ◂ q) ∙* r = p ◂ (q ∙* r)

  sym* : ∀ {C} {R : Rel C} {A B} {x : inter A} {y : inter B} 
       → *SymClosure R x y → *SymClosure R y x
  sym* rfl* = rfl*
  sym* (p ◂ r) = sym* r ∙* ⟪ symsym p ⟫
  instance
    *SymClosure-Eq : ∀ {C} {R : Rel C} → Eq (*SymClosure R)
    *SymClosure-Eq .rfl = rfl*
    *SymClosure-Eq .sym = sym*
    *SymClosure-Eq ._∙_ = _∙*_

    coed-eq : ∀ {C} {R : Rel C} → ⦃ Eq R ⦄ → Eq (Cohd R) 
    coed-eq .rfl {x = coe p _}           = coh p p rfl
    coed-eq .sym (coh p q P)             = coh q p (sym P) 
    coed-eq ._∙_ (coh p _ P) (coh _ q Q) = coh p q (P ∙ Q)

open RelationUtils public

Sub Γ Δ = Coed sub (λ (Γ₁ , Δ₁) (Γ₂ , Δ₂) → (Γ₁ ≈C Γ₂) × (Δ₁ ≈C Δ₂)) (Γ , Δ) 

_≈T_ = *SymClosure _≋T_
_≈s_ = Cohd _≈s′_

data Ctx where
  ε   : Ctx
  _,_ : (Γ : Ctx) → Ty Γ → Ctx

data _≈C_ where
  ε   : ε ≈C ε 
  _,_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Γ₁ ≈C Γ₂ → A₁ ≈T A₂ → Γ₁ , A₁ ≈C Γ₂ , A₂

module Eq-≈C where
  rflC : ∀ {Γ} → Γ ≈C Γ
  rflC {ε} = ε
  rflC {Γ , A} = rflC , rfl
  symC : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → Γ₂ ≈C Γ₁
  symC ε = ε
  symC (Γ , A) = symC Γ , sym A
  _∙C_ : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ≈C Γ₂ → Γ₂ ≈C Γ₃ → Γ₁ ≈C Γ₃
  ε ∙C ε = ε
  (Γ , A) ∙C (Δ , B) = (Γ ∙C Δ) , (A ∙ B)

instance 
  Eq-≈C : Eq _≈C_
  Eq-≈C .rfl = Eq-≈C.rflC
  Eq-≈C .sym = Eq-≈C.symC
  Eq-≈C ._∙_ = Eq-≈C._∙C_

data Ty Γ where
  U  : Ty Γ
  El : Tm Γ U → Ty Γ
  Π  : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
  
_[_] : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ

Tm Γ A = Coed tm (λ (_ , A₁) (_ , A₂) → A₁ ≈T A₂) (Γ , A)

data Sub′ where
  wk  : ∀ {Γ A} → Sub′ (Γ , A) Γ
  <_> : ∀ {Γ A} (M : Tm′ Γ A) → Sub′ Γ (Γ , A)
  _↑_ : ∀ {Γ Δ} (δ : Sub′ Γ Δ) → ∀ A 
      → Sub′ (Γ , (A [ coe (rfl , rfl) δ ])) (Δ , A)

_≈t′_  : ∀ {Γ₁ Γ₂ A₁ A₂} → Tm′ Γ₁ A₁ → Tm′ Γ₂ A₂ → Set
_≈t′_ = *SymClosure _≋t′_


data _≈s′_ where
  wk  : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → Γ₁ ≈C Γ₂ → A₁ ≈T A₂ 
      → wk {A = A₁} ≈s′ wk {A = A₂}
  [_,_]<_> : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm′ Γ₁ A₁} {M₂ : Tm′ Γ₂ A₂} 
           → Γ₁ ≈C Γ₂ → A₁ ≈T A₂ → M₁ ≈t′ M₂ → < M₁ > ≈s′ < M₂ >
  _↑_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub′ Γ₁ Δ₁} {δ₂ : Sub′ Γ₂ Δ₂} {A₁ A₂}
      → δ₁ ≈s′ δ₂ → A₁ ≈T A₂ → δ₁ ↑ A₁ ≈s′ δ₂ ↑ A₂

module Eq-≈s′ where
  rfls : ∀ {Γ Δ} (δ : Sub′ Δ Γ) → δ ≈s′ δ
  rfls wk = wk rfl rfl
  rfls < M > = [ rfl , rfl ]< rfl >
  rfls (δ ↑ A) = rfls δ ↑ rfl
  syms : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub′ Δ₁ Γ₁} {δ₂ : Sub′ Δ₂ Γ₂} → δ₁ ≈s′ δ₂ 
       → δ₂ ≈s′ δ₁ 
  syms (wk Γ A) = wk (sym Γ) (sym A)
  syms [ Γ , A ]< M > = [ sym Γ , sym A ]< sym M >
  syms (δ ↑ A) = syms δ ↑ sym A
  _∙s_ : ∀ {Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃} 
           {δ₁ : Sub′ Δ₁ Γ₁} {δ₂ : Sub′ Δ₂ Γ₂} {δ₃ : Sub′ Δ₃ Γ₃} 
       → δ₁ ≈s′ δ₂ → δ₂ ≈s′ δ₃ → δ₁ ≈s′ δ₃
  wk Γ A ∙s wk Δ B = wk (Γ ∙ Δ) (A ∙ B)
  [ Γ , A ]< M > ∙s [ Δ , B ]< N > = [ Γ ∙ Δ , A ∙ B ]< M ∙ N >
  (δ ↑ A) ∙s (σ ↑ B) = (δ ∙s σ) ↑ (A ∙ B) 

instance
  Eq-≈s′ : Eq _≈s′_
  Eq-≈s′ .rfl {x = δ} = Eq-≈s′.rfls δ
  Eq-≈s′ .sym = Eq-≈s′.syms
  Eq-≈s′ ._∙_ = Eq-≈s′._∙s_

wks : ∀ {Γ A} → Sub (Γ , A) Γ
wks = coe (rfl , rfl) wk

-- Could we use coe-s₁/coe-s₂ instead here?
<_>s : ∀ {Γ A} (M : Tm′ Γ A) → Sub Γ (Γ , A)
< M >s = coe (rfl , rfl) < M >

<_>st : ∀ {Γ A} (M : Tm Γ A) → Sub Γ (Γ , A)
< coe p M >st = coe ({!!} , {!!}) < M >

coe-T : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → Ty Γ₁ → Ty Γ₂
coh-T : ∀ {Γ₁ Γ₂} (Γ : Γ₁ ≈C Γ₂) → ∀ A → coe-T Γ A ≈T A

_↑s_ : ∀ {Γ Δ} (δ : Sub Γ Δ) → ∀ A → Sub (Γ , (A [ δ ])) (Δ , A)

data Var′ where
  vz : ∀ {Γ A} → Var′ (Γ , A) (A [ wks ])
  vs : ∀ {Γ A B} → Var′ Γ A → Var′ (Γ , B) (A [ wks ])

data Tm′ where
  var : ∀ {Γ A} → Var′ Γ A → Tm′ Γ A
  lam : ∀ {Γ A B} → Tm (Γ , A) B → Tm′ Γ (Π A B)
  app : ∀ {Γ A B} → Tm Γ (Π A B) → (M : Tm′ Γ A) → Tm′ Γ (B [ < M >s ])

_≈t_ = Cohd _≈t′_

_[_]t : ∀ {Γ Δ A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A [ δ ])

coe-t : ∀ {Γ₁ Γ₂ A₁ A₂} → A₁ ≈T A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂
coe-t p (coe q M) = coe (q ∙ p) M

coh-t : ∀ {Γ₁ Γ₂ A₁} {A₂ : Ty Γ₂} (A : A₁ ≈T A₂) (M  : Tm Γ₁ A₁) 
      → coe-t A M ≈t M 
coh-t p (coe q M) = coh _ _ rfl

data _≋T_ where
  U  : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → U {Γ₁} ≋T U {Γ₂}
  El : ∀ {Γ₁ Γ₂} {M₁ : Tm Γ₁ U} {M₂ : Tm Γ₂ U} → M₁ ≈t M₂ → El M₁ ≋T El M₂
  Π  : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂} → A₁ ≈T A₂ → B₁ ≈T B₂
     → Π A₁ B₁ ≋T Π A₂ B₂
    
  _[_]≈ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂} {δ₁ : Sub Δ₁ Γ₁} {δ₂ : Sub Δ₂ Γ₂} 
       → A₁ ≈T A₂ → δ₁ ≈s δ₂ → A₁ [ δ₁ ] ≋T A₂ [ δ₂ ]

  U[]  : ∀ {Γ Δ} {δ : Sub Δ Γ} → U [ δ ] ≋T U {Δ}
  El[] : ∀ {Γ Δ} {δ : Sub Δ Γ} {M} 
       → El M [ δ ] ≋T El (coe-t ⟪ U[] ¹⟫ (M [ δ ]t))
  Π[]  : ∀ {Γ Δ} {δ : Sub Δ Γ} {A B} → Π A B [ δ ] ≋T Π (A [ δ ]) (B [ δ ↑s A ])

coe (p , q) δ ↑s A 
  = coe ((p , ⟪ coh-T _ _ [ coh _ _ rfl ]≈ ¹⟫) , (q , coh-T _ _)) 
        (δ ↑ coe-T (sym q) A)

coe-s₁ : ∀ {Γ₁ Γ₂ Δ} (Γ : Γ₁ ≈C Γ₂) → Sub Γ₁ Δ → Sub Γ₂ Δ
coe-s₁ Γ (coe (p , Δ) δ) = coe ((p ∙ Γ) , Δ) δ

coh-s₁ : ∀ {Γ₁ Γ₂ Δ} (Γ : Γ₁ ≈C Γ₂) (δ : Sub Γ₁ Δ) → coe-s₁ Γ δ ≈s δ 
coh-s₁ Γ (coe (p , Δ) δ) = coh ((p ∙ Γ) , Δ) (p , Δ) rfl

coe-s₂ : ∀ {Γ Δ₁ Δ₂} (Δ : Δ₁ ≈C Δ₂) → Sub Γ Δ₁ → Sub Γ Δ₂
coe-s₂ Δ (coe (Γ , p) δ) = coe (Γ , (p ∙ Δ)) δ

coh-s₂ : ∀ {Γ Δ₁ Δ₂} (Δ : Δ₁ ≈C Δ₂) (δ : Sub Γ Δ₁) → coe-s₂ Δ δ ≈s δ 
coh-s₂ Δ (coe (Γ , p) δ) = coh (Γ , (p ∙ Δ)) (Γ , p) rfl

coe-T Γ U = U
coe-T Γ (El M) = El (coe-t ⟪ U Γ ¹⟫ M)
coe-T Γ (Π A B) = Π (coe-T Γ A) (coe-T (Γ , sym (coh-T _ _)) B)
-- coe-T Γ (A [ δ ]) = A [ coe-s₁ Γ δ ]

coh-T Γ U = ⟪ U Γ ⁻¹⟫
coh-T Γ (El M) = ⟪ El (coh-t _ _) ¹⟫
coh-T Γ (Π A B) = ⟪ Π (coh-T _ _) (coh-T _ _) ¹⟫
-- coh-T Γ (A [ δ ]) = ⟪ rfl [ coh-s₁ _ _ ] ¹⟫

_[_]t-ctx : ∀ {Γ Δ A} → Tm Γ A → Sub Δ Γ → Ctx
M [ δ ]t-ctx with M [ δ ]t
... | coe {B = Γ , _} _ _ = Γ

_[_]t-ty : ∀ {Γ Δ A} (M : Tm Γ A) (δ : Sub Δ Γ) → Ty (M [ δ ]t-ctx)
M [ δ ]t-ty with M [ δ ]t
... | coe {B = _ , A} _ _ = A

_[_]t-tm : ∀ {Γ Δ A} (M : Tm Γ A) (δ : Sub Δ Γ) 
         → Tm′ (M [ δ ]t-ctx) (M [ δ ]t-ty)
M [ δ ]t-tm with M [ δ ]t
... | coe _ M = M

≈t↑≈C : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} → M₁ ≈t M₂ → Γ₁ ≈C Γ₂

≈s′↑≈C₁ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub′ Γ₁ Δ₁} {δ₂ : Sub′ Γ₂ Δ₂}
       → δ₁ ≈s′ δ₂ → Γ₁ ≈C Γ₂
≈s′↑≈C₁ (wk Γ A) = Γ , A
≈s′↑≈C₁ [ Γ , A ]< M > = Γ
≈s′↑≈C₁ (δ ↑ A) = ≈s′↑≈C₁ δ , ⟪ A [ coh _ _ δ ]≈ ¹⟫

≈s↑≈C₁ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂}
       → δ₁ ≈s δ₂ → Γ₁ ≈C Γ₂
≈s↑≈C₁ (coh (p , _) (q , _) δ) = sym p ∙ ≈s′↑≈C₁ δ ∙ q

≈T↑≈C : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ → Γ₁ ≈C Γ₂
≈T↑≈C rfl* = rfl
≈T↑≈C (U Γ ¹ ◂ r) = Γ ∙ ≈T↑≈C r
≈T↑≈C (El M ¹ ◂ r) = ≈t↑≈C M ∙ ≈T↑≈C r
≈T↑≈C (Π A B ¹ ◂ r) = ≈T↑≈C A ∙ ≈T↑≈C r
≈T↑≈C (A [ δ ]≈ ¹ ◂ r) = ≈s↑≈C₁ δ ∙ ≈T↑≈C r
≈T↑≈C (U[] ¹ ◂ r) = ≈T↑≈C r
≈T↑≈C (El[] ¹ ◂ r) = ≈T↑≈C r
≈T↑≈C (Π[] ¹ ◂ r) = ≈T↑≈C r
≈T↑≈C (x ⁻¹ ◂ r) = {!   !}

app-t :  ∀ {Γ A B} → Tm Γ (Π A B) → (M : Tm Γ A) → Tm Γ (B [ < M >st ])
app-t M (coe p N) 
  = coe (⟪ coh-T ({!!} , p) _ [ coh-s₂ ({!!}, p) < N >s ]≈ ⁻¹⟫ ∙ {!!}) 
  (app (coe-t ⟪ Π p (coh-T ({!!} , sym p) _) ⁻¹⟫ M) N)

_[_]t′ : ∀ {Γ Δ A} → Tm′ Γ A → (δ : Sub Δ Γ) → Tm Δ (A [ δ ])

coe p M [ δ ]t = coe-t ⟪ p [ coh-s₂ (sym (≈T↑≈C p)) {!!} ]≈ ¹⟫ (M [ {!!} ]t′)

var x [ δ ]t′ = {!   !}
lam M [ δ ]t′ = coe ⟪ Π[] ⁻¹⟫ (lam (M [ δ ↑s _ ]t))
app M N [ δ ]t′ = coe-t {!!} (app-t (coe-t ⟪ Π[] ¹⟫ (M [ δ ]t)) (N [ δ ]t′))



_[_]v :  ∀ {Γ Δ A} → Var′ Γ A → (δ : Sub Δ Γ) → Tm Δ (A [ δ ])
x [ coe p wk ]v = coe ⟪ {!!} [ {!!} ]≈ ⁻¹⟫ (var (vs x))
x [ coe p < M > ]v = {!   !}
x [ coe p (δ ↑ A) ]v = {!   !} 

-- We need to be able to handle a coed substitutions
-- _[_]v :  ∀ {Γ Δ A} → Var′ Γ A → (δ : Sub′ Δ Γ) → Tm Δ (A [ coe (rfl , rfl) δ ])
-- x [ wk ]v       = coe rfl (var (vs x))
-- vz [ < M > ]v   = coe {!!} M
-- vs x [ < M > ]v = coe {!!} (var x)
-- vz [ δ ↑ A ]v   = coe {!!} (var vz)
-- vs x [ δ ↑ A ]v = coe-t {!!} (x [ δ ]v [ coe (rfl , rfl) wk ]t)

data _≈v′_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Var′ Γ₁ A₁ → Var′ Γ₂ A₂ → Set where
  vz : ∀ {Γ₁ Γ₂ A₁ A₂} → vz {Γ₁} {A₁} ≈v′ vz {Γ₂} {A₂}
  vs : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} {x₁ : Var′ Γ₁ A₁} {x₂ : Var′ Γ₂ A₂}
     → x₁ ≈v′ x₂ → vs {B = B₁} x₁ ≈v′ vs {B = B₂} x₂

data _≋t′_ where
  var : ∀ {Γ₁ Γ₂ A₁ A₂} {x₁ : Var′ Γ₁ A₁} {x₂ : Var′ Γ₂ A₂}
      → x₁ ≈v′ x₂ → var x₁ ≋t′ var x₂
  lam : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} {M₁ : Tm (Γ₁ , A₁) B₁} {M₂ : Tm (Γ₂ , A₂) B₂}
      → M₁ ≈t M₂ → lam M₁ ≋t′ lam M₂ 

  β : ∀ {Γ A B} {M : Tm (Γ , A) B} {N} 
    → app (coe rfl (lam M)) N ≋t′ (M [ < N >s ]t-tm)
  -- I am not sure if eta is derivable...
  -- η : ∀ {Γ A B} {M : Tm′ Γ (Π A B)} 
  --     → lam (coe rfl (app (coe-t ⟪ Π[] ¹⟫ (M [ coe (rfl , rfl) wk ]t′)) 
  --       (var vz))) ≋t′ M
  
-- Π-inj₂ : ∀ {A B}

-- _[_]t-ctx≈ : ∀ {Γ Δ A} (M : Tm Γ A) (δ : Sub Δ Γ) → M [ δ ]t-ctx ≈C Δ
-- coe p (var x) [ δ ]t-ctx≈ = {!   !}
-- coe p (lam M) [ δ ]t-ctx≈ = rfl
-- THIS would be definitionally true if we used Prop
-- coe p (app (coe s M) N) [ coe (q , r) δ ]t-ctx≈
--   = subst id {!!} (coe rfl N [ coe-s₂ (sym (≈T↑≈C p)) (coe (q , r) δ) ]t-ctx≈)
  -- = {!coe (sym (coh-T (≈T↑≈C p) _)) N [ (coe (q , r) δ) ]t-ctx≈!}
  -- = coe {!!} N [ (coe (q , r) δ) ]t-ctx≈
  -- where foo = coe {!!} N [ (coe (q , r) δ) ]t-ctx≈
  -- where foo = coe rfl N [ coe-s₂ (sym (≈T↑≈C p)) δ ]t-ctx≈

_[_]t′-ctx≈ : ∀ {Γ Δ A} (M : Tm′ Γ A) (δ : Sub Δ Γ) 
            → coe rfl M [ δ ]t-ctx ≈C Δ
var x [ δ ]t′-ctx≈ = {!   !}
lam M [ δ ]t′-ctx≈ = rfl
app M N [ δ ]t′-ctx≈ = N [ δ ]t′-ctx≈

-- proj₂≈ : ∀ (a

_[_]t-ctx≈ : ∀ {Γ Δ A} (M : Tm Γ A) (δ : Sub Δ Γ) → M [ δ ]t-ctx ≈C Δ
coe p (var x) [ δ ]t-ctx≈ = {!   !}
coe p (lam M) [ δ ]t-ctx≈ = rfl
-- Very hacky
coe p (app M N) [ δ ]t-ctx≈ 
  = subst id (cong (λ x → proj₁ (Coed.B (N [ coe (_ , x) _ ]t′)) ≈C _) help)
    (N [ coe-s₂ (sym (≈T↑≈C p)) δ ]t′-ctx≈)
  where 
    foo = {!N [ coe-s₂ (sym (≈T↑≈C p)) δ ]t′-ctx≈!}
    help : (proj₂ (Coed.p δ) ∙ sym (≈T↑≈C p)) ∙ sym rfl 
         ≡ (proj₂ (Coed.p δ) ∙ sym (≈T↑≈C p))
    help = {!!} -- This is true, but ugh - relying on it is awkward and
                  -- to properly support will need to require this equation
                  -- holds in all equality impls
                  -- Note we have no hope of proving slightly more tricky
                  -- equations like sym p ∙ p ≡ rfl
                  --
                  -- I think correct way to handle this would be some sort of 
                  -- congruence lemma for proj₁ (Coed.B ...) 

≈t′↑≈C : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm′ Γ₁ A₁} {M₂ : Tm′ Γ₂ A₂} → M₁ ≈t′ M₂ → Γ₁ ≈C Γ₂
≈t′↑≈C rfl* = {!   !}
≈t′↑≈C (var x ¹ ◂ r) = {!   !}
≈t′↑≈C (lam M ¹ ◂ r) = {!   !}
≈t′↑≈C (β ¹ ◂ r) = {!!} ∙ ≈t′↑≈C r
≈t′↑≈C (M ⁻¹ ◂ r) = {!   !}

≈t↑≈C (coh p q M) = {!   !}

-- (proj₁
--        (Coed.B
--         (N [
--          coe
--          (proj₁ (Coed.p δ) ,
--           ((proj₂ (Coed.p δ) Eq-≈C.∙C Eq-≈C.symC (≈T↑≈C p)) Eq-≈C.∙C
--            Eq-≈C.symC Eq-≈C.rflC))
--          (Coed.raw δ)
--          ]t′))
--        ≈C Δ)
--       ≡
--       (proj₁
--        (Coed.B
--         (N [
--          coe
--          (proj₁ (Coed.p δ) ,
--           (proj₂ (Coed.p δ) Eq-≈C.∙C Eq-≈C.symC (≈T↑≈C p)))
--          (Coed.raw δ)
--          ]t′))
--        ≈C Δ)


app′′ : ∀ {Γ A₁ A₂ B} (A : A₁ ≈T A₂) 
      → Tm′ Γ (Π A₁ B) → (M : Tm′ Γ A₂) → Tm′ Γ (B [ < coe (sym A) M >st ])


app′ : ∀ {Γ A B} → Tm Γ (Π A B) → (M : Tm Γ A) → Tm Γ (B [ < M >st ])
app′ (coe p M) (coe q N) = coe {!!} (app′′ {!!} {!M!} N)

lam′′ : ∀ {Γ A B} → Tm′ (Γ , A) B → Tm′ Γ (Π A B)

-- Oooh - we can eliminate Tm from lam!
-- This means only app needs Tm, and we can resolve this by adding just one
-- equation
lam′ : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
lam′ (coe {Δ , _} p M) with ≈T↑≈C p
lam′ (coe {(Δ , _) , _} p M) | (_ , q) = coe ⟪ Π q p ¹⟫ (lam′′ M)
  -- where foo = {!≈T↑≈C p!}


U [ δ ] = U
El M [ δ ] = {!!} -- El (M [ {!!} ]t)
Π A B [ δ ] = {!   !}
 