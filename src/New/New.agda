{-# OPTIONS --prop #-} 

open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (tt) renaming (⊤ to Unit)

module New.New where

module PropUtils where
  infixr 2 _∧_
  infixr 1 _∨_

  data ⊤ : Prop where tt : ⊤
  
  data ⊥ : Prop where

  record _∧_ (P Q : Prop) : Prop where
    constructor _,_
    eta-equality
    field
      proj₁ : P
      proj₂ : Q
  open _∧_ public

  data _∨_ (P Q : Prop) : Prop where
    inj₁ : P → P ∨ Q
    inj₂ : Q → P ∨ Q
  
  ∨-elim : ∀ {P Q} {R : Prop} → P ∨ Q → (P → R) → (Q → R) → R
  ∨-elim (inj₁ p) f g = f p
  ∨-elim (inj₂ q) f g = g q

  -- Unclear if this variation is actually helpful at all
  ∨-depelim : ∀ {P Q} {R : P ∨ Q → Prop} (pq : P ∨ Q) 
          → (∀ p → R (inj₁ p)) → (∀ q → R (inj₂ q)) → R pq
  ∨-depelim (inj₁ p) f g = f p
  ∨-depelim (inj₂ q) f g = g q

  data Squash (P : Set) : Prop where
    sq : P → Squash P

  sq-elim : ∀ {P : Set} {Q : Prop} → Squash P → (P → Q) → Q
  sq-elim (sq p) f = f p

open PropUtils public

infix 50 _[_]t*
infix 50 _[_]t
infix 50 _[_]T
infix 50 _[_]T*
infix 50 _El[_]

infixl 5 _◂_

data Ctx  : Set
data Ty   : Ctx → Set
data Var  : ∀ Γ → Ty Γ → Set
data Tm   : ∀ Γ → Ty Γ → Set
data Sub  : Ctx → Ctx → Set
data Subs : Ctx → Ctx → Set

data Ctx where
  ε : Ctx
  _,_ : ∀ Γ → Ty Γ → Ctx

data Ty where
  U      : ∀ {Γ} → Ty Γ
  _El[_] : ∀ {Γ Δ} → Tm Γ U → Subs Δ Γ → Ty Δ
  Π      : ∀ {Γ} A → Ty (Γ , A) → Ty Γ

_[_]T : ∀ {Γ Δ} → Ty Γ → Sub Δ Γ → Ty Δ

data Sub where
  wk  : ∀ {Γ A} → Sub (Γ , A) Γ
  <_> : ∀ {Γ A} → Tm Γ A → Sub Γ (Γ , A)
  _↑_ : ∀ {Γ Δ} (δ : Sub Δ Γ) A → Sub (Δ , A [ δ ]T) (Γ , A)

data Subs where
  idₛ : ∀ {Γ} → Subs Γ Γ
  _◂_ : ∀ {Γ Δ Σ} → Subs Δ Γ → Sub Σ Δ → Subs Σ Γ

_∘ₛ_ : ∀ {Γ Δ Σ} → Subs Δ Γ → Subs Σ Δ → Subs Σ Γ
δ ∘ₛ idₛ = δ
δ ∘ₛ (σ ◂ γ) = (δ ∘ₛ σ) ◂ γ

U [ δ ]T = U
(A El[ σ ]) [ δ ]T = A El[ σ ◂ δ ] 
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ↑ A ]T)

data Var where
  vz : ∀ {Γ A} → Var (Γ , A) (A [ wk ]T)
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ , B) (A [ wk ]T)

_[_]T* : ∀ {Γ Δ} → Ty Γ → Subs Δ Γ → Ty Δ
A [ idₛ ]T* = A
A [ δ ◂ σ ]T* = A [ δ ]T* [ σ ]T

-- Interesting: Can get here with no holes other than Tm

module RelationUtils where
  infix 10 _¹
  infix 10 _⁻¹

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

  SynUArg ctx        = Unit
  SynUArg ty         = Ctx
  SynUArg tm         = ∃ Ty
  SynUArg sub        = Ctx × Ctx
  SynUArg (coed C)   = CoedIdx (SynUArg C)

  inter {ctx}  _          = Ctx
  inter {ty}   Γ          = Ty Γ
  inter {tm}   (Γ , A)    = Tm Γ A
  inter {sub}  (Γ , Δ)    = Sub Γ Δ
  inter {coed C} (wrap A) = Coed C (idx-rel C) A

  -- idx-rel ctx                        = _≡_
  -- idx-rel ty                         = _≈C_
  -- idx-rel tm  (_ , A₁) (_ , A₂)      = A₁ ≈T A₂
  -- idx-rel sub (Γ₁ , Δ₁) (Γ₂ , Δ₂)    = (Γ₁ ≈C Γ₂) × (Δ₁ ≈C Δ₂)
  -- idx-rel (coed C) (wrap x) (wrap y) = idx-rel C x y

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

_≈C_ : Ctx → Ctx → Prop

_≈t_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Prop

_≈s_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Sub Δ₁ Γ₁ → Sub Δ₂ Γ₂ → Prop

_≈S_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Subs Δ₁ Γ₁ → Subs Δ₂ Γ₂ → Prop

data _~S_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Subs Δ₁ Γ₁ → Subs Δ₂ Γ₂ → Set where
  idₛ : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → idₛ {Γ₁} ~S idₛ {Γ₂}
  _◂_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ Σ₁ Σ₂} {δ₁ : Subs Δ₁ Γ₁} {δ₂ : Subs Δ₂ Γ₂} 
          {σ₁ : Sub Σ₁ Δ₁} {σ₂ : Sub Σ₂ Δ₂} 
      → δ₁ ≈S δ₂ → σ₁ ≈s σ₂ → (δ₁ ◂ σ₁) ~S (δ₂ ◂ σ₂)
  
  -- Note this rule is very restrictive, but I think it is ok because later we
  -- will be able to derive the more general form, this is just for 
  -- bootstrapping
  wk-comm : ∀ {Γ Δ A} {δ : Sub Δ Γ}
          → (idₛ ◂ wk ◂ δ ↑ A) ~S (idₛ ◂ δ ◂ wk {A = A [ δ ]T})

δ₁ ≈S δ₂ = Squash (δ₁ ~S δ₂)

_[_]t : ∀ {Γ Δ A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T)

_[_]t* : ∀ {Γ Δ A} → Tm Γ A → (δ : Subs Δ Γ) → Tm Δ (A [ δ ]T*)
M [ idₛ ]t* = M
M [ δ ◂ σ ]t* = M [ δ ]t* [ σ ]t

_≈T_ : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Prop

ε ≈C ε = ⊤
(Γ₁ , A₁) ≈C (Γ₂ , A₂) = Γ₁ ≈C Γ₂ ∧ A₁ ≈T A₂
_ ≈C _ = ⊥

U {Γ₁} ≈T U {Γ₂} = Γ₁ ≈C Γ₂
_≈T_ {Γ₁} {Γ₂} (A₁ El[ δ₁ ]) (A₂ El[ δ₂ ]) 
  = (A₁ ≈t A₂ ∧ δ₁ ≈S δ₂) ∨ (Γ₁ ≈C Γ₂ ∧ A₁ [ δ₁ ]t* ≈t A₂ [ δ₂ ]t*)
Π A₁ B₁ ≈T Π A₂ B₂ = B₁ ≈T B₂
_ ≈T _ = ⊥

wk {Γ₁} {A₁} ≈s wk {Γ₂} {A₂} = Γ₁ ≈C Γ₂ ∧ A₁ ≈T A₂ 
<_> {Γ₁} {A₁} M₁ ≈s <_> {Γ₂} {A₂} M₂ = Γ₁ ≈C Γ₂ ∧ A₁ ≈T A₂ ∧ M₁ ≈t M₂
(δ₁ ↑ A₁) ≈s (δ₂ ↑ A₂) = δ₁ ≈s δ₂ ∧ A₁ ≈T A₂
_ ≈s _ = ⊥

-- We can define views over the ≈ relations like so
module ~ where
  data _~T_ : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Set where
    U      : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → U {Γ₁} ~T U {Γ₂}
    _El[_] : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂} {δ₁ : Subs Δ₁ Γ₁} {δ₂ : Subs Δ₂ Γ₂} 
          → A₁ ≈t A₂ → δ₁ ≈S δ₂ → A₁ El[ δ₁ ] ~T A₂ El[ δ₂ ]
    Elβ    : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂} {δ₁ : Subs Δ₁ Γ₁} {δ₂ : Subs Δ₂ Γ₂} 
          → Δ₁ ≈C Δ₂ → A₁ [ δ₁ ]t* ≈t A₂ [ δ₂ ]t* → A₁ El[ δ₁ ] ~T A₂ El[ δ₂ ] 
    Π      : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂} 
          → B₁ ≈T B₂ → Π A₁ B₁ ~T Π A₂ B₂

  ≈T→~T : ∀ {Γ₁ Γ₂} (A₁ : Ty Γ₁) (A₂ : Ty Γ₂) → A₁ ≈T A₂ → Squash (A₁ ~T A₂)
  ≈T→~T U U p = sq (U p)
  ≈T→~T (A₁ El[ δ₁ ]) (A₂ El[ δ₂ ]) (inj₁ (A , δ)) = sq (A El[ δ ])
  ≈T→~T (A₁ El[ δ₁ ]) (A₂ El[ δ₂ ]) (inj₂ (Γ , A)) = sq (Elβ Γ A)
  ≈T→~T (Π A₁ B₁) (Π A₂ B₂) p = sq (Π p)

  ~T→≈T : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ~T A₂ → A₁ ≈T A₂
  ~T→≈T (U Γ) = Γ
  ~T→≈T (A El[ δ ]) = inj₁ (A , δ)
  ~T→≈T (Elβ Γ A) = inj₂ (Γ , A)
  ~T→≈T (Π B) = B

,-inj₁ : ∀ {Γ₁ Γ₂} A₁ A₂ → (Γ₁ , A₁) ≈C (Γ₂ , A₂) → Γ₁ ≈C Γ₂
,-inj₁ _ _ = proj₁

,-inj₂ : ∀ {Γ₁ Γ₂} A₁ A₂ → (Γ₁ , A₁) ≈C (Γ₂ , A₂) → A₁ ≈T A₂
,-inj₂ _ _ = proj₂

[]T≈ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} A₁ A₂ (δ₁ : Sub Δ₁ Γ₁) (δ₂ : Sub Δ₂ Γ₂)
      → A₁ ≈T A₂ → δ₁ ≈s δ₂ → A₁ [ δ₁ ]T ≈T A₂ [ δ₂ ]T

≈T↑≈C : ∀ {Γ₁ Γ₂} (A₁ : Ty Γ₁) (A₂ : Ty Γ₂) → A₁ ≈T A₂ → Γ₁ ≈C Γ₂
≈s↑≈C₁ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} (δ₁ : Sub Δ₁ Γ₁) (δ₂ : Sub Δ₂ Γ₂) → δ₁ ≈s δ₂ → Δ₁ ≈C Δ₂
≈S↑≈C₁ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} {δ₁ : Subs Δ₁ Γ₁} {δ₂ : Subs Δ₂ Γ₂} → δ₁ ~S δ₂ → Δ₁ ≈C Δ₂


[]T≈ U U δ₁ δ₂ A δ = ≈s↑≈C₁ δ₁ δ₂ δ
[]T≈ (A₁ El[ σ₁ ]) (A₂ El[ σ₂ ]) δ₁ δ₂ (inj₁ (A , σ)) δ = inj₁ (A , sq (σ ◂ δ))
[]T≈ (A₁ El[ σ₁ ]) (A₂ El[ σ₂ ]) δ₁ δ₂ (inj₂ (Γ , A)) δ = inj₂ (≈s↑≈C₁ δ₁ δ₂ δ , {!!})
[]T≈ (Π A₁ B₁) (Π A₂ B₂) δ₁ δ₂ B δ 
  = []T≈ B₁ B₂ (δ₁ ↑ A₁) (δ₂ ↑ A₂) B (δ , (,-inj₂ A₁ A₂ (≈T↑≈C B₁ B₂ B)))

≈s↑≈C₁ wk wk p = p
≈s↑≈C₁ < M₁ > < M₂ > (Δ , _ , _) = Δ
≈s↑≈C₁ (δ₁ ↑ A₁) (δ₂ ↑ A₂) (δ , A) = ≈s↑≈C₁ δ₁ δ₂ δ , []T≈ A₁ A₂ δ₁ δ₂ A δ

≈S↑≈C₁ (idₛ Γ) = Γ
≈S↑≈C₁ (δ ◂ σ) = ≈s↑≈C₁ _ _ σ
≈S↑≈C₁ wk-comm = {!!} , {!!}

≈T↑≈C U U p = p
≈T↑≈C (A₁ El[ δ₁ ]) (A₂ El[ δ₂ ]) (inj₁ (A , δ)) = {!!}
≈T↑≈C (A₁ El[ δ₁ ]) (A₂ El[ δ₂ ]) (inj₂ (Γ , A)) = Γ
≈T↑≈C (Π A₁ B₁) (Π A₂ B₂) p = ,-inj₁ A₁ A₂ (≈T↑≈C B₁ B₂ p)


data Tm where
  var : ∀ {Γ A} → Var Γ A → Tm Γ A
  lam : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
  app : ∀ {Γ₁ Γ₂ A₁ A₂ B} (A : A₁ ≈T A₂) 
      → Tm Γ₁ (Π A₁ B) → (N : Tm Γ₂ A₂) → Tm Γ₂ ({!B!} [ < N > ]T)


_[_]v₁ : ∀ {Γ Δ A} → Var Γ A → (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T)
x [ wk ]v₁ = var (vs x)
vz [ < M > ]v₁ = {!   !}
vs x [ < M > ]v₁ = {!   !}
x [ δ ↑ A ]v₁ = {!   !}


M [ δ ]t = {!!}


