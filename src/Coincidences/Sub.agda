{-# OPTIONS --rewriting --local-confluence-check --prop #-}

open import Coincidences.Utils
open import Coincidences.Syntax

module Coincidences.Sub where

infixl 100 _[_]w _[_]s _[_]wv _[_]wtm _[_]sv _[_]stm 
infixl 100 _[_]stys _[_]wtys
infixl 100 _[_]semtys

data Wk  : Ctx → Ctx → Set
data Sub : Ctx → Ctx → Set
⟦_⟧w : Wk Δ Γ  → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c
⟦_⟧s : Sub Δ Γ → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c
_[_]w  : Ty Γ → Wk Δ Γ  → Ty Δ
_[_]s  : Ty Γ → Sub Δ Γ → Ty Δ
_[_]wβ : ∀ A (δ : Wk Δ Γ)  → ⟦ A [ δ ]w ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧w
_[_]sβ : ∀ A (δ : Sub Δ Γ) → ⟦ A [ δ ]s ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧s

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
⟦ δ ↑ A ⟧w (ρ , M) = ⟦ δ ⟧w ρ , subst (λ AB → El (AB ρ)) (A [ δ ]wβ) M

⟦ < M > ⟧s ρ       = ρ , ⟦ M ⟧tm ρ
⟦ δ ↑ A ⟧s (ρ , M) = ⟦ δ ⟧s ρ , subst (λ AB → El (AB ρ)) (A [ δ ]sβ) M

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

⊥' [ δ ]wβ = refl
Π' A B [ δ ]wβ 
  = cong (Πsem ⟦ A [ δ ]w ⟧T) (B [ δ ↑ A ]wβ)
  ∙ sym (dcong₂ Πsem (sym A≡) ([]w-helper B δ A≡))
  where A≡ = A [ δ ]wβ
El' A [ δ ]wβ = refl

⊥' [ δ ]sβ = refl
Π' A B [ δ ]sβ 
  = cong (Πsem ⟦ A [ δ ]s ⟧T) (B [ δ ↑ A ]sβ)
  ∙ sym (dcong₂ Πsem (sym A≡) ([]s-helper B δ A≡))
  where A≡ = A [ δ ]sβ
El' A [ δ ]sβ = refl

{-# REWRITE _[_]wβ _[_]sβ #-}

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

_↑s_ : ∀ {Γ Δ} (δ : SemSub Δ Γ) A → SemSub (Δ ,s (A ∘ δ)) (Γ ,s A)
(δ ↑s A) (ρ , x) = δ ρ , x

data Tys : Ctx → Set
_++_ : ∀ Γ → Tys Γ → Ctx

data Tys where
  ε   : Tys Γ
  _,_ : ∀ Δ → Ty (Γ ++ Δ) → Tys Γ

Γ ++ ε       = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

_[_]wtys : Tys Γ → Wk Δ Γ → Tys Δ
_[_]stys : Tys Γ → Sub Δ Γ → Tys Δ

_↑↑w_ : ∀ (δ : Wk Δ Γ) Γ′ → Wk (Δ ++ Γ′ [ δ ]wtys) (Γ ++ Γ′)
_↑↑s_ : ∀ (δ : Sub Δ Γ) Γ′ → Sub (Δ ++ Γ′ [ δ ]stys) (Γ ++ Γ′)

ε [ δ ]wtys = ε
(Γ′ , A) [ δ ]wtys = Γ′ [ δ ]wtys , A [ δ ↑↑w Γ′ ]w

ε [ δ ]stys = ε
(Γ′ , A) [ δ ]stys = Γ′ [ δ ]stys , A [ δ ↑↑s Γ′ ]s

δ ↑↑w ε = δ     
δ ↑↑w (Γ′ , A) = (δ ↑↑w Γ′) ↑ A 

δ ↑↑s ε = δ     
δ ↑↑s (Γ′ , A) = (δ ↑↑s Γ′) ↑ A

data SemTys : SemCtx → Set₁

_++s_ : ∀ Γ → SemTys Γ → SemCtx

data SemTys where
  ε   : ∀ {Γ} → SemTys Γ
  _,_ : ∀ {Γ} Γ′ → SemTy (Γ ++s Γ′) → SemTys Γ

Γ ++s ε = Γ
Γ ++s (Γ′ , A) = (Γ ++s Γ′) ,s A

_[_]semtys : ∀ {Γ Δ} → SemTys Γ → SemSub Δ Γ → SemTys Δ
_↑↑sem_ : ∀ {Γ Δ} (δ : SemSub Δ Γ) Γ′ → SemSub (Δ ++s Γ′ [ δ ]semtys) (Γ ++s Γ′)

ε [ δ ]semtys = ε
(Γ′ , A) [ δ ]semtys = Γ′ [ δ ]semtys , A ∘ (δ ↑↑sem Γ′)

δ ↑↑sem ε = δ
δ ↑↑sem (Γ′ , A) = (δ ↑↑sem Γ′) ↑s A

private module Congruences where
  Tys≡ = cong Tys
  SemTys≡ = cong SemTys
  Wk≡ = cong₂ Wk
  Sub≡ = cong₂ Sub

  _++≡_ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′} (Γ≡ : Γ₁ ≡ Γ₂) → Γ₁′ ≡[ Tys≡ Γ≡ ]≡ Γ₂′
        → Γ₁ ++ Γ₁′ ≡ Γ₂ ++ Γ₂′
  refl ++≡ refl = refl

  ,tys≡ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) 
            (Γ≡′ : Γ₁′ ≡[ Tys≡ Γ≡ ]≡ Γ₂′)
        → A₁ ≡[ Ty≡ (Γ≡ ++≡ Γ≡′) ]≡ A₂ → Γ₁′ , A₁ ≡[ Tys≡ Γ≡ ]≡ Γ₂′ , A₂ 
  ,tys≡ refl refl refl = refl

  _++s≡_ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′} (Γ≡ : Γ₁ ≡ Γ₂) → Γ₁′ ≡[ SemTys≡ Γ≡ ]≡ Γ₂′
        → Γ₁ ++s Γ₁′ ≡ Γ₂ ++s Γ₂′
  refl ++s≡ refl = refl

  ,semtys≡ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) 
            (Γ≡′ : Γ₁′ ≡[ SemTys≡ Γ≡ ]≡ Γ₂′)
        → A₁ ≡[ SemTy≡ (Γ≡ ++s≡ Γ≡′) ]≡ A₂ → Γ₁′ , A₁ ≡[ SemTys≡ Γ≡ ]≡ Γ₂′ , A₂ 
  ,semtys≡ refl refl refl = refl

  ,proj≡₁ : ∀ {Γ Γ₁′ Γ₂′} {A₁ : Ty (Γ ++ Γ₁′)} {A₂ : Ty (Γ ++ Γ₂′)} 
          → Tys._,_ Γ₁′ A₁ ≡ Tys._,_ Γ₂′ A₂ → Γ₁′ ≡ Γ₂′
  ,proj≡₁ refl = refl

  ,proj≡s₁ : ∀ {Γ Γ₁′ Γ₂′} {A₁ : SemTy (Γ ++s Γ₁′)} {A₂ : SemTy (Γ ++s Γ₂′)} 
          → SemTys._,_ Γ₁′ A₁ ≡ SemTys._,_ Γ₂′ A₂ → Γ₁′ ≡ Γ₂′
  ,proj≡s₁ refl = refl

  ↑s≡ : ∀ {Γ₁ Γ₂ Δ δ₁ δ₂} {A : SemTy Δ} (Γ≡ : Γ₁ ≡ Γ₂)
            (δ≡ : δ₁ ≡[ SemSub≡ Γ≡ refl ]≡ δ₂) 
        → δ₁ ↑s A ≡[ SemSub≡ (Γ≡ ,s≡ ([]sem≡ Γ≡ refl (erefl A) δ≡)) refl 
       ]≡ δ₂ ↑s A
  ↑s≡ refl refl = refl 

  []w≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
       → A₁ ≡[ Ty≡ Γ≡ ]≡ A₂ → δ₁ ≡[ Wk≡ Δ≡ Γ≡ ]≡ δ₂
       → A₁ [ δ₁ ]w ≡[ Ty≡ Δ≡ ]≡ A₂ [ δ₂ ]w
  []w≡ refl refl refl refl = refl

  []s≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
       → A₁ ≡[ Ty≡ Γ≡ ]≡ A₂ → δ₁ ≡[ Sub≡ Δ≡ Γ≡ ]≡ δ₂
       → A₁ [ δ₁ ]s ≡[ Ty≡ Δ≡ ]≡ A₂ [ δ₂ ]s
  []s≡ refl refl refl refl = refl

  ⟦⟧w≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
       → δ₁ ≡[ Wk≡ Γ≡ Δ≡ ]≡ δ₂ 
       → ⟦ δ₁ ⟧w ≡[ SemSub≡ ⟦ Γ≡ ⟧c≡ ⟦ Δ≡ ⟧c≡ ]≡ ⟦ δ₂ ⟧w
  ⟦⟧w≡ refl refl refl = refl

  ⟦⟧s≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
       → δ₁ ≡[ Sub≡ Γ≡ Δ≡ ]≡ δ₂ 
       → ⟦ δ₁ ⟧s ≡[ SemSub≡ ⟦ Γ≡ ⟧c≡ ⟦ Δ≡ ⟧c≡ ]≡ ⟦ δ₂ ⟧s
  ⟦⟧s≡ refl refl refl = refl

  []wtm≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ M₁ M₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
             (A≡ : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂) (δ≡ : δ₁ ≡[ Wk≡ Δ≡ Γ≡ ]≡ δ₂)
         → M₁ ≡[ Tm≡ Γ≡ A≡ ]≡ M₂
         → M₁ [ δ₁ ]wtm ≡[ Tm≡ Δ≡ ([]sem≡ ⟦ Δ≡ ⟧c≡ ⟦ Γ≡ ⟧c≡ A≡ (⟦⟧w≡ Δ≡ Γ≡ δ≡)) 
        ]≡ M₂ [ δ₂ ]wtm
  []wtm≡ refl refl refl refl refl = refl

  []stm≡ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A₁ A₂ M₁ M₂ δ₁ δ₂} (Γ≡ : Γ₁ ≡ Γ₂) (Δ≡ : Δ₁ ≡ Δ₂)
             (A≡ : A₁ ≡[ SemTy≡ ⟦ Γ≡ ⟧c≡ ]≡ A₂) (δ≡ : δ₁ ≡[ Sub≡ Δ≡ Γ≡ ]≡ δ₂)
         → M₁ ≡[ Tm≡ Γ≡ A≡ ]≡ M₂
         → M₁ [ δ₁ ]stm ≡[ Tm≡ Δ≡ ([]sem≡ ⟦ Δ≡ ⟧c≡ ⟦ Γ≡ ⟧c≡ A≡ (⟦⟧s≡ Δ≡ Γ≡ δ≡)) 
        ]≡ M₂ [ δ₂ ]stm
  []stm≡ refl refl refl refl refl = refl

  wk≡ : ∀ {Γ₁ Γ₂ A₁ A₂} (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ Γ≡ ]≡ A₂) 
      → wk ≡[ Wk≡ (Γ≡ ,≡ A≡) Γ≡ ]≡ wk 
  wk≡ refl refl = refl

open Congruences public

⟦_⟧tys : Tys Γ → SemTys ⟦ Γ ⟧c

⟦++⟧tys≡ : ∀ (Γ′ : Tys Γ) → ⟦ Γ ++ Γ′ ⟧c ≡ ⟦ Γ ⟧c ++s ⟦ Γ′ ⟧tys

⟦ ε ⟧tys = ε
⟦ Γ′ , A ⟧tys = ⟦ Γ′ ⟧tys , (subst SemTy (⟦++⟧tys≡ Γ′) ⟦ A ⟧T)

⟦⟧tys≡ : ∀ {Γ₁ Γ₂ Γ₁′ Γ₂′} (Γ≡ : Γ₁ ≡ Γ₂) → Γ₁′ ≡[ Tys≡ Γ≡ ]≡ Γ₂′ 
        → ⟦ Γ₁′ ⟧tys ≡[ SemTys≡ ⟦ Γ≡ ⟧c≡ ]≡ ⟦ Γ₂′ ⟧tys
⟦⟧tys≡ refl refl = refl

⟦⟧tys≡-lemma : ∀ {Γ₁ Γ₂} {A : SemTy Γ₁} (Γ≡ : Γ₁ ≡ Γ₂) 
             → A ≡[ SemTy≡ Γ≡ ]≡ (subst SemTy Γ≡ A)
⟦⟧tys≡-lemma refl = refl

⟦++⟧tys≡ ε = refl
⟦++⟧tys≡ (Γ′ , A) = Γ≡′ ,s≡ ⟦⟧tys≡-lemma Γ≡′
  where Γ≡′ = ⟦++⟧tys≡ Γ′
  
{-# REWRITE ⟦++⟧tys≡ #-}
