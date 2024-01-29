{-# OPTIONS --without-K #-}

open import Data.Product using (Σ; ∃; _×_)
  renaming (_,_ to infixl 6 _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; refl)
open import Function.Base using (id)
open import Data.Maybe using (Maybe; map; just; nothing)
open import Data.Unit using (⊤)

module Syntax where

postulate todo : ∀ {A : Set} → A

_≡[_]≡_ : ∀ {A B : Set} → A → A ≡ B → B → Set
A ≡[ p ]≡ B = subst id p A ≡ B

data Wrap {a} (A : Set a) : Set a where
  wrap : A → Wrap A

infixl 6 _,_
infix 5 _++_
infix 4 _≋C_
infix 4 _≋T_
infix 4 _≋Ts_
infix 4 _≋t_
infix 4 _≋s_
infix 4 _≈C_
infix 4 _≈T_
infix 4 _≈Ts_
infix 4 _≈t_
infix 4 _≈s_
infix 4 _↭C_
infix 4 _↭T_ 
infix 4 _↭Ts_
infix 4 _↭t_ 
infix 4 _↭s_ 
infix 4 _~T_
infix 4 _≈[_]T_

data Ctx : Set
data Ty  (Γ : Ctx) : Set
data Tys (Γ : Ctx) : Set
data Tm  : (Γ : Ctx) → Ty Γ → Set
data Sub : Ctx → Ctx → Set

-- Ideally I would make this a completely separate module, but we define
-- data types, and therefore would run into 
-- https://github.com/agda/agda/issues/3209
module HetEq where
  infixr 5 _∙_
  infix 2 _¹
  infix 2 _⁻¹

  -- We work inside of a closed inductive-recursive universe to dodge the pain 
  -- of dealing with universe levels (and also work with heterogeneous equations
  -- WITHOUT axiom K!!)
  data SynUCon : Set where
    ctx ty tys tm sub : SynUCon

    -- Utilities
    maybe  : SynUCon → SynUCon
    exists : SynUCon → SynUCon → SynUCon

  SynUArg : SynUCon → Set

  inter : ∀ {C} → SynUArg C → Set

  SynUArg ctx       = ⊤
  SynUArg ty        = Ctx
  SynUArg tys       = Ctx
  SynUArg tm        = ∃ Ty
  SynUArg sub       = Ctx × Ctx
  -- We wrap the argument type here to retain injectivity
  SynUArg (maybe C)      = Wrap (SynUArg C)
  SynUArg (exists C₁ C₂) = Σ (SynUArg C₁) (λ x → inter x → SynUArg C₂)

  inter {ctx} _                = Ctx
  inter {ty}  Γ                = Ty Γ
  inter {tys} Γ                = Tys Γ
  inter {tm}  (Γ , A)          = Tm Γ A
  inter {sub} (Γ , Δ)          = Sub Γ Δ
  inter {maybe C} (wrap A)     = Maybe (inter {C} A)
  inter {exists C₁ C₂} (A , B) = Σ (inter A) (λ x → inter (B x))

  Rel : SynUCon → Set₁
  Rel C = ∀ {A B : SynUArg C} → inter A → inter B → Set

  data SymClosure {C} (R : Rel C) : Rel C where
    _¹  : ∀ {A B} {x : inter A} {y : inter B}
        → R x y → SymClosure R x y
    _⁻¹ : ∀ {A B} {x : inter A} {y : inter B}
        → R x y → SymClosure R y x

  data *Closure {C} (R : Rel C) : Rel C where
    rfl : ∀ {A} {x : inter A} → *Closure R x x
    trs : ∀ {A B C} {x : inter A} {y : inter B} {z : inter C}
        → R y z → *Closure R x y → *Closure R x z

  *SymClosure : ∀ {C} → Rel C → Rel C
  *SymClosure r = *Closure (SymClosure r)

  ⟦_⟧ : ∀ {C} {R : Rel C} {A B} {x : inter A} {y : inter B} 
      → R x y → *SymClosure R x y
  ⟦ p ⟧ = trs (p ¹) rfl

  ⟦_⟧⁻¹ : ∀ {C} {R : Rel C} {A B} {x : inter A} {y : inter B} 
        → R x y → *SymClosure R y x
  ⟦ p ⟧⁻¹ = trs (p ⁻¹) rfl

  _∙_ : ∀ {C} {R : Rel C} {A B C} {x y z}
      → *SymClosure R {B} {C} y z 
      → *SymClosure R {A} {B} x y 
      → *SymClosure R {A} {C} x z
  rfl ∙ q = q
  trs x p ∙ q = trs x (p ∙ q)

  symsym : ∀ {C} {R : Rel C} {A B} {x y}
      → SymClosure R {A} {B} x y
      → SymClosure R {B} {A} y x
  symsym (p  ¹) = p ⁻¹
  symsym (p ⁻¹) = p  ¹

  sym : ∀ {C} {R : Rel C} {A B} {x y}
      → *SymClosure R {A} {B} x y
      → *SymClosure R {B} {A} y x
  sym rfl = rfl
  sym (trs p q) = sym q ∙ trs (symsym p) rfl

  Pred : SynUCon → Set₁
  Pred C = ∀ {A : SynUArg C} → inter A → Set

  -- Utilities for lifiting proofs
  module _ {C₁ C₂} {R₁ : Rel C₁} {R₂ : Rel C₂} (P : Pred C₁)
           (P-prop : ∀ {A} {x y : inter A} (Px : P x) (Py : P y) (p : x ≡ y) 
                      → Px ≡[ cong P p ]≡ Py)
           (P-inj : ∀ {A B} {x : inter A} {y : inter B} 
                  → SymClosure R₁ x y → P x → P y) 
           where
           
    lift-proofP : ∀ {A B : SynUArg C₁}
                   {C : ∀ {AB} (xy : inter AB) → P xy → SynUArg C₂}
                   (f : ∀ {AB} (xy : inter AB) (Pxy : P xy) → inter (C xy Pxy))
                   (proof : ∀ {A B} {x : inter A} {y : inter B} 
                              (Px : P x) (Py : P y)
                          → R₁ x y → *SymClosure R₂ (f x Px) (f y Py)) 
                   {x : inter A} {y : inter B}
                   (Px : P x) (Py : P y)
               → *SymClosure R₁ x y → *SymClosure R₂ (f x Px) (f y Py)
    lift-proofP f p Px Py rfl with P-prop Px Py refl
    ... | refl = rfl
    lift-proofP f p Px Py (trs (q  ¹) r) = p Pz Py q ∙ lift-proofP f p Px Pz r
      where Pz = P-inj (q ⁻¹) Py
    lift-proofP f p Px Py (trs (q ⁻¹) r) 
      = sym (p Py Pz q) ∙ lift-proofP f p Px Pz r
      where Pz = P-inj (q ¹) Py

  module _ {C₁ C₂} {R₁ : Rel C₁} {R₂ : Rel C₂} where
    -- This is certainly definable in terms of lift-proofP, but it's small
    -- enough regardless that I am unconvinced whether doing so would be worth
    -- it
    lift-proof : ∀ {A B : SynUArg C₁}
                   {C : ∀ {AB} (xy : inter {C₁} AB) → SynUArg C₂}
                   (f : ∀ {AB} (xy : inter AB) → inter (C xy))
                   (proof : ∀ {A B} {x : inter A} {y : inter B} 
                          → R₁ x y → *SymClosure R₂ (f x) (f y)) 
                   {x : inter A} {y : inter B}
                 → *SymClosure R₁ x y → *SymClosure R₂ (f x) (f y)
    lift-proof f p rfl            = rfl
    lift-proof f p (trs (q  ¹) r) = p q ∙ lift-proof f p r
    lift-proof f p (trs (q ⁻¹) r) = sym (p q) ∙ lift-proof f p r

open HetEq public

data _≋C_  : Ctx → Ctx → Set
data _≋T_  : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Set
data _≋Ts_ : ∀ {Γ₁ Γ₂} → Tys Γ₁ → Tys Γ₂ → Set
data _≋t_  : ∀ {Γ₁ Γ₂ A₁ A₂} → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Set
data _≋s_  : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Sub Γ₁ Δ₁ → Sub Γ₂ Δ₂ → Set

_↭C_  : Ctx → Ctx → Set
_↭C_  = SymClosure _≋C_
_↭T_  : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Set
_↭T_  = SymClosure _≋T_
_↭Ts_ : ∀ {Γ₁ Γ₂} → Tys Γ₁ → Tys Γ₂ → Set
_↭Ts_ = SymClosure _≋Ts_
_↭t_  : ∀ {Γ₁ Γ₂ A₁ A₂} → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Set
_↭t_ = SymClosure _≋t_
_↭s_  : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Sub Γ₁ Δ₁ → Sub Γ₂ Δ₂ → Set
_↭s_ = SymClosure _≋s_

_≈C_  : Ctx → Ctx → Set
_≈C_  = *SymClosure _≋C_
_≈T_  : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Set
_≈T_  = *SymClosure _≋T_ 
_≈Ts_ : ∀ {Γ₁ Γ₂} → Tys Γ₁ → Tys Γ₂ → Set
_≈Ts_ = *SymClosure _≋Ts_
_≈t_  : ∀ {Γ₁ Γ₂ A₁ A₂} → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Set
_≈t_  = *SymClosure _≋t_
_≈s_  : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Sub Γ₁ Δ₁ → Sub Γ₂ Δ₂ → Set
_≈s_  = *SymClosure _≋s_

_≈[_]T_ : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Γ₁ ≈C Γ₂ → Ty Γ₂ → Set
A₁ ≈[ _ ]T A₂ = A₁ ≈T A₂ 

_~T_ : ∀ {Γ} → Ty Γ → Ty Γ → Set
_~T_ = _≈T_

-- Adding meta-language Σ-types to the syntax universe made the syntax no longer
-- strictly positive
-- We could avoid this by adding only exactly the Σ-types we need, but that
-- is quite inconvenient
{-# NO_POSITIVITY_CHECK #-}
data Ctx where
  ε   : Ctx
  _,_ : (Γ : Ctx) → Ty Γ → Ctx

data Ty Γ where
  U  : Ty Γ
  El : Tm Γ U → Ty Γ
  Π  : (A : Ty Γ) → Ty (Γ , A) → Ty Γ

_++_ : ∀ Γ → Tys Γ → Ctx

data Tys Γ where
  ε   : Tys Γ
  _,_ : (Δ : Tys Γ) → Ty (Γ ++ Δ) → Tys Γ

Γ ++ ε = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

_[_]T : ∀ {Γ Δ} → Ty Γ → Sub Δ Γ → Ty Δ

data Sub where
  coe₁ : ∀ {Γ₁ Γ₂ Δ} → Γ₁ ↭C Γ₂ → Sub Γ₁ Δ → Sub Γ₂ Δ
  coe₂ : ∀ {Γ Δ₁ Δ₂} → Δ₁ ↭C Δ₂ → Sub Γ Δ₁ → Sub Γ Δ₂

  -- Note that requiring the same Γ here in argumemt and return positions
  -- prevents implementing coercions recursively. It is unclear to me which 
  -- approach is nicer.
  wk  : ∀ {Γ A} → Sub (Γ , A) Γ
  <_> : ∀ {Γ A} → Tm Γ A → Sub Γ (Γ , A)
  _↑_ : ∀ {Γ Δ} (δ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , A [ δ ]T) (Δ , A)

data Tm where
  coe   : ∀ {Γ₁ Γ₂ A₁ A₂} → A₁ ↭T A₂ → Tm Γ₁ A₁ → Tm Γ₂ A₂

  app   : ∀ {Γ A B} → Tm Γ (Π A B) → (M : Tm Γ A) → Tm Γ (B [ < M > ]T)
  lam   : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
  _[_] : ∀ {Γ Δ A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T)
  vz    : ∀ {Γ A} → Tm (Γ , A) (A [ wk ]T)

U [ δ ]T = U
El M [ δ ]T = El (M [ δ ])
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ↑ A ]T)

_[_]Ts : ∀ {Γ Δ} → Tys Γ → Sub Δ Γ → Tys Δ
_↑↑_   : ∀ {Γ Δ} (δ : Sub Δ Γ) (Σ : Tys Γ) → Sub (Δ ++ Σ [ δ ]Ts) (Γ ++ Σ)

ε [ δ ]Ts = ε
(Σ , A) [ δ ]Ts = Σ [ δ ]Ts , A [ δ ↑↑ Σ ]T

δ ↑↑ ε = δ
δ ↑↑ (Σ , A) = (δ ↑↑ Σ) ↑ A

data _≋C_ where
  ε   : Ctx.ε ≋C Ctx.ε
  _,_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Γ₁ ≈C Γ₂ → A₁ ≈T A₂ → Γ₁ , A₁ ≋C Γ₂ , A₂

data _≋T_ where
  U  : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → U {Γ₁} ≋T U {Γ₂}
  El : ∀ {Γ₁ Γ₂} {M₁ : Tm Γ₁ U} {M₂ : Tm Γ₂ U} → M₁ ≈t M₂ → El M₁ ≋T El M₂ 
  -- Note I think we could elide A₁ ≈T A₂ as this is derivable from B₁ ≈T B₂ 
  Π  : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂} 
     → A₁ ≈T A₂ → B₁ ≈T B₂ → Π A₁ B₁ ≋T Π A₂ B₂

data _≋Ts_ where
  ε   : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → Tys.ε {Γ₁} ≋Ts Tys.ε {Γ₂}
  _,_ : ∀ {Γ₁ Γ₂} {Δ₁ : Tys Γ₁} {Δ₂ : Tys Γ₂} {A₁ A₂} 
      → Δ₁ ≈Ts Δ₂ → A₁ ≈T A₂ → Δ₁ , A₁ ≋Ts Δ₂ , A₂

data _≋t_ where
  coh   : ∀ {Γ₁ Γ₂ A₁} {A₂ : Ty Γ₂} {M : Tm Γ₁ A₁} (A : A₁ ↭T A₂) 
        → Tm.coe A M ≋t M

  lam   : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} {M₁ : Tm (Γ₁ , A₁) B₁} {M₂ : Tm (Γ₂ , A₂) B₂} 
        → M₁ ≈t M₂ → lam M₁ ≋t lam M₂
  app   : ∀ {Γ₁ Γ₂ A₁ A₂ B₁ B₂} {M₁ : Tm Γ₁ (Π A₁ B₁)} {M₂ : Tm Γ₂ (Π A₂ B₂)}
            {N₁ N₂}
        → M₁ ≈t M₂ → N₁ ≈t N₂ → app M₁ N₁ ≋t app M₁ N₂
  vz    : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ 
        → vz {A = A₁} ≋t vz {A = A₂}
  _[_]≋ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} 
            {δ₁ : Sub Δ₁ Γ₁} {δ₂ : Sub Δ₂ Γ₂} 
        → M₁ ≈t M₂ → δ₁ ≈s δ₂ → M₁ [ δ₁ ] ≋t M₂ [ δ₂ ]

  β     : ∀ {Γ A B} {M : Tm (Γ , A) B} {N} → app (lam M) N ≋t M [ < N > ]
  η     : ∀ {Γ A B} {M : Tm Γ (Π A B)} 
        → Tm.lam (app (M [ wk ]) (vz {A = A})) ≋t M
    
  <>-comm  : ∀ {Γ Δ A Σ B N} (M : Tm ((Γ , A) ++ Σ) B) (δ : Sub Δ Γ)
           → M [ (δ ↑ A) ↑↑ Σ ] [ < N [ δ ] > ↑↑ (Σ [ δ ↑ A ]Ts) ] 
          ≋t M [ < N > ↑↑ Σ ] [ δ ↑↑ (Σ [ < N > ]Ts) ]
  wk-vz-id : ∀ {Γ B Δ A} (M : Tm ((Γ , B) ++ Δ) A) 
           → M [ (wk ↑ B) ↑↑ Δ ] [ < vz > ↑↑ (Δ [ wk ↑ B ]Ts) ] 
          ≋t M
  -- ...

  -- We need at least all of these equations:
  -- M [ wk     ] [ < N >  ] ≡ M                   (wk-<>-id)
  -- M [ wk ↑ B ] [ < vz > ] ≡ M                   (wk-vz-id)
  -- M [ wk     ] [ δ ↑ B  ] ≡ M [ δ     ] [ wk ]  (wk-comm)
  -- M [ δ ↑ B  ] [ < N >  ] ≡ M [ < N > ] [ δ  ]  (<>-comm)

  -- vz    [ < M > ] ≡ M                           (vz<>)
  -- vz    [ δ ↑ A ] ≡ vz                          (vz[])
  -- lam M [ δ     ] ≡ lam (M [ δ ↑ B ])           (lam[])

data _≋s_ where
  coh₁ : ∀ {Γ₁ Γ₂ Δ δ} (Γ : Γ₁ ↭C Γ₂) → coe₁ {Δ = Δ} Γ δ ≋s δ
  coh₂ : ∀ {Γ Δ₁ Δ₂ δ} (Δ : Δ₁ ↭C Δ₂) → coe₂ {Γ = Γ} Δ δ ≋s δ

  wk  : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ 
      → wk {A = A₁} ≋s wk {A = A₂}
  <_> : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Tm Γ₁ A₁} {M₂ : Tm Γ₂ A₂} 
      → M₁ ≈t M₂ → < M₁ > ≋s < M₂ >
  _↑_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Sub Γ₁ Δ₁} {δ₂ : Sub Γ₂ Δ₂} {A₁ A₂}
      → δ₁ ≈s δ₂ → A₁ ≈T A₂ → δ₁ ↑ A₁ ≋s δ₂ ↑ A₂
    