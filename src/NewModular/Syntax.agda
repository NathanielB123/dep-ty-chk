{-# OPTIONS --prop #-}
{-# OPTIONS --show-irrelevant #-}

open import NewModular.PropUtils

open import Data.Product using (∃; _×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; subst)
  renaming (sym to sym≡)
open import Function.Base using (id)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Level using (Lift; lift)

module NewModular.Syntax where

-- I am not sure I believe starting with normal forms is a good idea
-- Specifically, I'm not sure what it gives us, and what it takes away is
-- pretty brutal (being able to separate definition of syntax and normalisation)
-- Plus, it's less extensible (no way to define typechecking based on reducing
-- to WHNFs)
-- It *is* unfortunate that equality for terms therefore cannot be purely
-- syntax directed, but I think that's a price worth paying (and we have to
-- deal with not-purely-syntax-directed type equality anyway)

-- Equality utils

_≡[_]≡_ : ∀ {a} {A B : Set a} → A → A ≡ B → B → Set a
x ≡[ refl ]≡ y = x ≡ y

depcong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c} 
             (f : (x : A) → B x → C) {x y u v} (xy : x ≡ y) 
         → u ≡[ cong B xy ]≡ v → f x u ≡ f y v
depcong₂ f refl refl = refl

coe≡ : ∀ {a} {A B : Set a} → A ≡ B → A → B
coe≡ = subst id

-- cong₂ : ∀ (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
-- cong₂ f refl refl = refl


-- End equality utils

-- infix 50 _[_]t*
-- infix 50 _[_]t
infix 50 _[_]T*
infix 50 _[_]T-raw
infix 50 _El[_]

infixl 5 _◂_

data Ctx     : Set
data Ty      : Ctx → Set
data Var     : ∀ Γ → Ty Γ → Set
data Nf      : ∀ Γ → Ty Γ → Set
data Ne      : ∀ Γ → Ty Γ → Set
data Tm      : ∀ Γ → Ty Γ → Set
data RawSub  : Ctx → Ctx → Set
Sub          : Ctx → Ctx → Set
data Subs    : Ctx → Ctx → Set

_≈C_ : Ctx → Ctx → Prop
_≈T_ : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Prop
_≈s_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Sub Δ₁ Γ₁ → Sub Δ₂ Γ₂ → Prop
_≈s-raw_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → RawSub Δ₁ Γ₁ → RawSub Δ₂ Γ₂ → Prop
_≈S_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Subs Δ₁ Γ₁ → Subs Δ₂ Γ₂ → Prop
_≈v_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Var Γ₁ A₁ → Var Γ₂ A₂ → Prop
_≈ne_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Ne Γ₁ A₁ → Ne Γ₂ A₂ → Prop
_≈nf_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Nf Γ₁ A₁ → Nf Γ₂ A₂ → Prop
_≈t_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Prop

data Ctx where
  ε   : Ctx
  _,_ : ∀ Γ → Ty Γ → Ctx

data Ty where
  U      : ∀ {Γ} → Ty Γ
  _El[_] : ∀ {Γ Δ} → Tm Γ U → Subs Δ Γ → Ty Δ
  Π      : ∀ {Γ} A → Ty (Γ , A) → Ty Γ

_[_]T-raw : ∀ {Γ Δ} → Ty Γ → RawSub Δ Γ → Ty Δ

data RawSub where
  wk  : ∀ {Γ A} → RawSub (Γ , A) Γ
  <_> : ∀ {Γ A} → Tm Γ A → RawSub Γ (Γ , A)
  _↑_ : ∀ {Γ Δ} (δ : RawSub Δ Γ) A → RawSub (Δ , A [ δ ]T-raw) (Γ , A)

data Subs where
  idₛ : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → Subs Γ₁ Γ₂
  _◂_ : ∀ {Γ Δ Σ} → Subs Δ Γ → Sub Σ Δ → Subs Σ Γ

_∘ₛ_ : ∀ {Γ Δ Σ} → Subs Δ Γ → Subs Σ Δ → Subs Σ Γ


_[_]T : ∀ {Γ Δ} → Ty Γ → Sub Δ Γ → Ty Δ
_↑s_ : ∀ {Γ Δ} (δ : Sub Δ Γ) A → Sub (Δ , A [ δ ]T) (Γ , A)

U [ δ ]T = U
(A El[ σ ]) [ δ ]T = A El[ σ ◂ δ ] 
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ↑s A ]T)

_[_]T* : ∀ {Γ Δ} → Ty Γ → Subs Δ Γ → Ty Δ

data Var where
  vz : ∀ {Γ A} → Var (Γ , A) (A [ wk ]T-raw)
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ , B) (A [ wk ]T-raw)

module RelationUtils where
  infix 10 _¹
  infix 10 _⁻¹

  data SynUCon : Set
  SynUArg : SynUCon → Set

  data SynUCon where
    ctx ty var nf ne tm sub : SynUCon
    coed : (C : SynUCon) → SynUCon

  inter : ∀ {C} → SynUArg C → Set

  idx-rel : ∀ C → SynUArg C → SynUArg C → Prop

  record Coed C (A : SynUArg C) : Set where
    constructor coe
    inductive
    eta-equality
    field
      {B} : SynUArg C
      p   : idx-rel C B A
      raw : inter B

  -- Wrapper to help type inference
  record CoedIdx (A : Set) : Set where
    constructor wrap
    inductive
    eta-equality
    field
      wrapped : A

  SynUArg ctx      = Unit
  SynUArg ty       = Ctx
  SynUArg var      = ∃ Ty
  SynUArg ne       = ∃ Ty
  SynUArg nf       = ∃ Ty
  SynUArg tm       = ∃ Ty
  SynUArg sub      = Ctx × Ctx
  SynUArg (coed C) = CoedIdx (SynUArg C)

  inter {ctx}    _        = Ctx
  inter {ty}     Γ        = Ty Γ
  inter {var}    (Γ , A)  = Var Γ A
  inter {ne}     (Γ , A)  = Ne Γ A
  inter {nf}     (Γ , A)  = Nf Γ A
  inter {tm}     (Γ , A)  = Tm Γ A
  inter {sub}    (Γ , Δ)  = RawSub Γ Δ
  inter {coed C} (wrap A) = Coed C A

  idx-rel ctx _ _                    = ⊤ 
  idx-rel ty                         = _≈C_
  idx-rel var (_ , A₁) (_ , A₂)      = A₁ ≈T A₂
  idx-rel ne  (_ , A₁) (_ , A₂)      = A₁ ≈T A₂
  idx-rel nf  (_ , A₁) (_ , A₂)      = A₁ ≈T A₂
  idx-rel tm  (_ , A₁) (_ , A₂)      = A₁ ≈T A₂
  idx-rel sub (Γ₁ , Δ₁) (Γ₂ , Δ₂)    = (Γ₁ ≈C Γ₂) ∧ (Δ₁ ≈C Δ₂)
  idx-rel (coed C) (wrap x) (wrap y) = idx-rel C x y

  Rel : SynUCon → Set₁
  Rel C = ∀ {A B : SynUArg C} → inter A → inter B → Prop

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

  -- This could probably become a record with eta-equality if that turns out
  -- to be convenient
  data Cohd {C A₁ A₂} (R : Rel C) : Coed C A₁ → Coed C A₂ → Prop where
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

Sub Δ Γ = Coed sub (Δ , Γ)

quote-nf : ∀ {Γ} {A} → Nf Γ A → Tm Γ A

data Ne where
  var : ∀ {Γ A} → Var Γ A → Ne Γ A
  app : ∀ {Γ₁ Γ₂ A₁ A₂ B} (A : A₁ ≈T A₂) 
      → Ne Γ₁ (Π A₁ B) → (N : Nf Γ₂ A₂) → Ne Γ₂ ({!B!} [ < quote-nf N > ]T-raw)

data Nf where
  ne  : ∀ {Γ A} → Ne Γ A → Nf Γ A
  lam : ∀ {Γ A B} → Nf (Γ , A) B → Nf Γ (Π A B)

_[_]T-coe : ∀ {Γ A} → Coed tm (Γ , A)

ε ≈C ε = ⊤
(Γ₁ , A₁) ≈C (Γ₂ , A₂) = Γ₁ ≈C Γ₂ ∧ A₁ ≈T A₂
_ ≈C _ = ⊥

_[_]t* : ∀ {Γ Δ A} → Tm Γ A → (δ : Subs Δ Γ) → Tm Δ (A [ δ ]T*)

U {Γ₁} ≈T U {Γ₂} = Γ₁ ≈C Γ₂
_≈T_ {Γ₁} {Γ₂} (A₁ El[ δ₁ ]) (A₂ El[ δ₂ ]) 
  = (A₁ ≈t A₂ ∧ δ₁ ≈S δ₂) ∨ (Γ₁ ≈C Γ₂ ∧ (A₁ [ δ₁ ]t*) ≈t (A₂ [ δ₂ ]t*))
Π A₁ B₁ ≈T Π A₂ B₂ = B₁ ≈T B₂
_ ≈T _ = ⊥

wk {Γ₁} {A₁} ≈s-raw wk {Γ₂} {A₂} = Γ₁ ≈C Γ₂ ∧ A₁ ≈T A₂ 
<_> {Γ₁} {A₁} M₁ ≈s-raw <_> {Γ₂} {A₂} M₂ = Γ₁ ≈C Γ₂ ∧ A₁ ≈T A₂ ∧ M₁ ≈t M₂
(δ₁ ↑ A₁) ≈s-raw (δ₂ ↑ A₂) = δ₁ ≈s-raw δ₂ ∧ A₁ ≈T A₂
_ ≈s-raw _ = ⊥

instance
  ≈C-Eq : Eq _≈C_
  ≈T-Eq : Eq _≈T_
  ≈nf-Eq : Eq _≈nf_
  ≈t-Eq : Eq _≈t_

coe-T : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → Ty Γ₁ → Ty Γ₂
coh-T : ∀ {Γ₁ Γ₂} (Γ : Γ₁ ≈C Γ₂) → ∀ A → coe-T Γ A ≈T A

coe-s₁ : ∀ {Γ Δ₁ Δ₂} → Δ₁ ≈C Δ₂ → Sub Δ₁ Γ → Sub Δ₂ Γ
coe-s₁ p (coe (Δ , Γ) δ) = coe (Δ ∙ p , Γ) δ

coe-s₂ : ∀ {Γ₁ Γ₂ Δ} → Γ₁ ≈C Γ₂ → Sub Δ Γ₁ → Sub Δ Γ₂
coe-s₂ p (coe (Δ , Γ) δ) = coe (Δ , (Γ ∙ p)) δ

coe-S₁ : ∀ {Γ Δ₁ Δ₂} → Δ₁ ≈C Δ₂ → Subs Δ₁ Γ → Subs Δ₂ Γ 
coe-S₁ p (idₛ Γ) = idₛ (sym p ∙ Γ)
coe-S₁ p (δ ◂ σ) = δ ◂ coe-s₁ p σ

coh-S₁ : ∀ {Γ Δ₁ Δ₂} (Δ : Δ₁ ≈C Δ₂) (δ : Subs Δ₁ Γ) → coe-S₁ Δ δ ≈S δ

coe-T p U = U
coe-T p (A El[ δ ]) = A El[ coe-S₁ p δ ]
coe-T p (Π A B) 
  = Π (coe-T p A) (coe-T (p , (sym {y = A} (coh-T _ A))) B)

coh-T p U           = sym p
coh-T p (A El[ δ ]) = inj₁ (rfl {x = A} , coh-S₁ _ δ)
coh-T p (Π A B)     = coh-T _ B

δ ∘ₛ (idₛ Γ) = coe-S₁ (sym Γ) δ
δ ∘ₛ (σ ◂ γ) = (δ ∘ₛ σ) ◂ γ

A [ idₛ Γ ]T* = coe-T (sym Γ) A
A [ δ ◂ σ ]T* = A [ δ ]T* [ σ ]T

,-inj₁ : ∀ {Γ₁ Γ₂} A₁ A₂ → (Γ₁ , A₁) ≈C (Γ₂ , A₂) → Γ₁ ≈C Γ₂
,-inj₁ _ _ = proj₁

,-inj₂ : ∀ {Γ₁ Γ₂} A₁ A₂ → (Γ₁ , A₁) ≈C (Γ₂ , A₂) → A₁ ≈T A₂
,-inj₂ _ _ = proj₂

[]T≈-raw : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} A₁ A₂ (δ₁ : RawSub Δ₁ Γ₁) (δ₂ : RawSub Δ₂ Γ₂)
      → A₁ ≈T A₂ → δ₁ ≈s-raw δ₂ → (A₁ [ δ₁ ]T-raw) ≈T (A₂ [ δ₂ ]T-raw)

≈T↑≈C : ∀ {Γ₁ Γ₂} (A₁ : Ty Γ₁) (A₂ : Ty Γ₂) → A₁ ≈T A₂ → Γ₁ ≈C Γ₂
≈s↑≈C₁-raw : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} (δ₁ : RawSub Δ₁ Γ₁) (δ₂ : RawSub Δ₂ Γ₂) 
           → δ₁ ≈s-raw δ₂ → Δ₁ ≈C Δ₂
≈S↑≈C₁ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} (δ₁ : Subs Δ₁ Γ₁) (δ₂ : Subs Δ₂ Γ₂)
       → δ₁ ≈S δ₂ → Δ₁ ≈C Δ₂


-- []T≈ U U δ₁ δ₂ A δ = ≈s↑≈C₁ δ₁ δ₂ δ
-- []T≈ (A₁ El[ σ₁ ]) (A₂ El[ σ₂ ]) δ₁ δ₂ (inj₁ (A , σ)) δ = inj₁ (A , sq (σ ◂ δ))
-- []T≈ (A₁ El[ σ₁ ]) (A₂ El[ σ₂ ]) δ₁ δ₂ (inj₂ (Γ , A)) δ = inj₂ (≈s↑≈C₁ δ₁ δ₂ δ , {!!})
-- []T≈ (Π A₁ B₁) (Π A₂ B₂) δ₁ δ₂ B δ 
--   = []T≈ B₁ B₂ (δ₁ ↑ A₁) (δ₂ ↑ A₂) B (δ , (,-inj₂ A₁ A₂ (≈T↑≈C B₁ B₂ B)))

≈s↑≈C₁-raw wk wk p = p
≈s↑≈C₁-raw < M₁ > < M₂ > (Δ , _ , _) = Δ
≈s↑≈C₁-raw (δ₁ ↑ A₁) (δ₂ ↑ A₂) (δ , A) 
  = ≈s↑≈C₁-raw δ₁ δ₂ δ , []T≈-raw A₁ A₂ δ₁ δ₂ A δ

-- ≈S↑≈C₁ (idₛ Γ) = Γ
-- ≈S↑≈C₁ (δ ◂ σ) = {!!} -- ≈s↑≈C₁ _ _ σ
-- ≈S↑≈C₁ wk-comm = {!!} , {!!}

≈T↑≈C U U p = p
≈T↑≈C (A₁ El[ δ₁ ]) (A₂ El[ δ₂ ]) (inj₁ (A , δ)) = ≈S↑≈C₁ δ₁ δ₂ δ
≈T↑≈C (A₁ El[ δ₁ ]) (A₂ El[ δ₂ ]) (inj₂ (Γ , A)) = Γ
≈T↑≈C (Π A₁ B₁) (Π A₂ B₂) p = ,-inj₁ A₁ A₂ (≈T↑≈C B₁ B₂ p)

data Tm where
  var : ∀ {Γ A} → Var Γ A → Tm Γ A
  lam : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
  app : ∀ {Γ₁ Γ₂ A₁ A₂ B} (A : A₁ ≈T A₂) 
      → Tm Γ₁ (Π A₁ B) → (N : Tm Γ₂ A₂) 
      → Tm Γ₂ (coe-T (≈T↑≈C A₁ A₂ A , A) B [ < N > ]T-raw)



module NbE where
  normalise : ∀ {Γ A} → Tm Γ A → Nf Γ A

  ⟦_⟧-ctx : Ctx → Set₁
  ⟦_⟧-ty  : ∀ {Γ} → Ty Γ → ⟦ Γ ⟧-ctx → Set₁
  ⟦_⟧-var : ∀ {Γ} {A : Ty Γ} → Var Γ A → (Γ′ : ⟦ Γ ⟧-ctx) → ⟦ A ⟧-ty Γ′
  ⟦_⟧-ne  : ∀ {Γ} {A : Ty Γ} → Ne Γ A → (Γ′ : ⟦ Γ ⟧-ctx) → ⟦ A ⟧-ty Γ′
  ⟦_⟧-nf  : ∀ {Γ} {A : Ty Γ} → Nf Γ A → (Γ′ : ⟦ Γ ⟧-ctx) → ⟦ A ⟧-ty Γ′
  ⟦_⟧-tm  : ∀ {Γ} {A : Ty Γ} → Tm Γ A → (Γ′ : ⟦ Γ ⟧-ctx) → ⟦ A ⟧-ty Γ′

  ⟦⟧≈C : ∀ Γ₁ Γ₂ → Γ₁ ≈C Γ₂ → ⟦ Γ₁ ⟧-ctx ≡ ⟦ Γ₂ ⟧-ctx

  ⟦ ε ⟧-ctx = Lift _ Unit
  ⟦ Γ , A ⟧-ctx = Σ ⟦ Γ ⟧-ctx ⟦ A ⟧-ty

  ⟦⟧≈C ε ε p = refl
  ⟦⟧≈C (Γ₁ , A₁) (Γ₂ , A₂) (p , q) = depcong₂ Σ (⟦⟧≈C Γ₁ Γ₂ p) {!!}

  ⟦ U ⟧-ty _ = Set
  -- Tying the knot and interpreting the term in order to interpret the type
  -- causes the termination checker to die, sad!
  ⟦ A El[ δ ] ⟧-ty Γ = Lift _ {!!} -- (⟦ A ⟧-tm {!!})
    -- where foo = ⟦ A ⟧-tm
  ⟦ Π A B ⟧-ty Γ = (x : ⟦ A ⟧-ty Γ) → ⟦ B ⟧-ty (Γ , x) 

  ⟦ ne x ⟧-nf = {!   !}
  ⟦ lam M ⟧-nf = λ Γ x → ⟦ M ⟧-nf (Γ , x)

  ⟦coe⟧ : ∀ {Γ₁ Γ₂ A} {Γ≈ : Γ₁ ≈C Γ₂} {⟦Γ⟧ : ⟦ Γ₂ ⟧-ctx}  
        → ⟦ coe-T Γ≈ A ⟧-ty ⟦Γ⟧ ≡ ⟦ A ⟧-ty (coe≡ (⟦⟧≈C Γ₂ Γ₁ (sym Γ≈)) ⟦Γ⟧)

-- ⟦ coe-T (≈T↑≈C A₁ A₂ A , A) B ⟧-ty (Γ , ⟦ N ⟧-tm Γ) ≡
--       ⟦ B ⟧-ty
--       (subst (λ x → x) (sym≡ (⟦⟧≈C Γ₁ Γ₂ (≈T↑≈C A₁ A₂ A))) Γ ,
--        subst (λ x → x) (⟦⟧-ty≈ A) (⟦ N ⟧-tm Γ))


  ⟦⟧-ty≈ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {⟦Γ⟧ : ⟦ Γ₂ ⟧-ctx} → (A≈ : A₁ ≈T A₂) 
         → ⟦ A₂ ⟧-ty ⟦Γ⟧ ≡ ⟦ A₁ ⟧-ty (coe≡ (sym≡ (⟦⟧≈C _ _ (≈T↑≈C A₁ A₂ A≈))) ⟦Γ⟧) 


  -- Even if the above termination error wasn't a problem, I'm somewhat
  -- concerned that these laws won't be provable without getting stuck on a
  -- loop. Interpreting the syntax relies on these laws, but these are laws
  -- *about* how the syntax gets interpreted.
  --
  -- Yet again the Type ↔ Term dependency kills us
  --
  -- I have hope that most of this can be salvaged into a development that
  -- focusses on syntax first and then considers normal forms, but without OTT
  -- this stuff will always be pretty painful
  ⟦[]T⟧ : ∀ {Γ} {C : Ty Γ} {A} {M : Tm Γ C} {Γ′} 
        → ⟦ A [ < M > ]T-raw ⟧-ty Γ′ ≡ ⟦ A ⟧-ty (Γ′ , ⟦ M ⟧-tm Γ′)

  -- Man, I wish we had OTT... 
  -- ⟦coe⟧′ would be judgementally the same as ⟦coe⟧...
  ⟦coe⟧′ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B : Ty (Γ₁ , A₁)} 
              {A≈ : A₁ ≈T A₂} 
             {⟦Γ⟧ : ⟦ Γ₂ ⟧-ctx} {⟦M⟧ : ⟦ A₂ ⟧-ty ⟦Γ⟧}
         → ⟦_⟧-ty {Γ = Γ₂ , A₂} (coe-T (≈T↑≈C A₁ A₂ A≈ , A≈) B) (⟦Γ⟧ , ⟦M⟧) 
         ≡ ⟦ B ⟧-ty (coe≡ (sym≡ (⟦⟧≈C Γ₁ Γ₂ (≈T↑≈C A₁ A₂ A≈))) ⟦Γ⟧ 
         , coe≡ (⟦⟧-ty≈ A≈) ⟦M⟧) 
         
  ⟦ var x ⟧-tm = {!   !}
  ⟦ lam M ⟧-tm = λ Γ x → ⟦ M ⟧-tm (Γ , x)    
  ⟦ app {A₁ = A₁} {A₂ = A₂} A M N ⟧-tm Γ 
    = coe≡ (sym≡ ⟦[]T⟧) (coe≡ (sym≡ ⟦coe⟧′) baz)
    where foo = ⟦ M ⟧-tm (coe≡ (sym≡ (⟦⟧≈C _ _ (≈T↑≈C A₁ A₂ A))) Γ)
          bar = ⟦ N ⟧-tm Γ
          baz = foo (coe≡ (⟦⟧-ty≈ A) bar)
 

