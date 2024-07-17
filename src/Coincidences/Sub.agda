{-# OPTIONS --prop --show-irrelevant --rewriting --local-confluence-check #-}

open import Coincidences.Utils
open import Coincidences.Syntax

module Coincidences.Sub where

infixl 100 _[_]w _[_]s _[_]wv _[_]wtm _[_]sv _[_]stm 
infixl 100 _[_]stys _[_]wtys
infixl 100 _[_]semtys

data Wk  : Ctx → Ctx → Set

⟦_⟧w : Wk Δ Γ  → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c
_[_]w  : Ty Γ → Wk Δ Γ  → Ty Δ
_[_]w≡ : ∀ A (δ : Wk Δ Γ)  → ⟦ A [ δ ]w ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧w

-- Prepare for a lot of duplication between weakenings/substitutions. 
-- I don't know how to get rid of this without Agda's termination checker
-- complaining.
data Wk where
  wk : Wk (Γ , A) Γ
  _↑_ : ∀ (δ : Wk Γ Δ) A → Wk (Γ , A [ δ ]w) (Δ , A)

_↑s_ : ∀ {Γ Δ} (δ : SemSub Δ Γ) A → SemSub (Δ ,s (A ∘ δ)) (Γ ,s A)
_↑s_ δ A (ρ , x) = δ ρ , x

⟦ wk ⟧w    = semwk _
⟦ δ ↑ A ⟧w (ρ , x) 
  = (⟦ δ ⟧w ↑s ⟦ A ⟧T) (ρ , subst (λ A[] → El (A[] ρ)) ((A [ δ ]w≡)) x) 

_[_]wtm  : ∀ {Γ A} → Tm Γ A → (δ : Wk Δ Γ)  → Tm Δ (A ∘ ⟦ δ ⟧w)

⊥' [ δ ]w = ⊥'
(Π' A B) [ δ ]w = Π' (A [ δ ]w) (B [ δ ↑ A ]w)
El' A [ δ ]w = El' (A [ δ ]wtm) 

-- TODO: These are just proofs on semantic substitutions, and so we could
-- probably turn these into rewrites and simplify a bunch of the below proofs.
[]-helper : ∀ {Γ Δ A A[]} (B : SemTy (Γ ,s A)) (δ : SemSub Δ Γ) 
               (p : A[] ≡ A ∘ δ) 
        → subst (SemTy ∘ (_ ,s_)) (sym p)
          (B ∘ (δ ↑s _))
        ≡ (λ (ρ , x) → B (δ ρ , subst (λ AB → El (AB ρ)) p x))
[]-helper B δ refl = refl

[]v-helper : ∀ {Γ A B} (p : A ≡ B)
       → subst (SemVal (Γ ,s A)) (cong (_∘ semwk _) p) 
               semvz
       ≡ (λ (ρ , x) → subst (λ AB → El (AB ρ)) p x)
[]v-helper refl = refl

[]tm-helper : ∀ {Γ Δ} (δ : SemSub Δ Γ) {A[]} 
                {A : SemTy Γ} {B : SemTy (Γ ,s A)} 
                (M : SemVal _ B) (A≡ : A[] ≡ _) B≡
            → subst (SemVal Δ) (Πsem≡ refl A≡ B≡)
              (λ ρ x → (M ∘ (δ ↑s A)) 
                       (ρ , subst (λ A[] → El (A[] ρ)) A≡ x))
            ≡ (λ ρ N → M (ρ , N)) ∘ δ
[]tm-helper _ _ refl refl = refl

⊥' [ δ ]w≡ = refl
Π' A B [ δ ]w≡ 
  = cong (Πsem ⟦ A [ δ ]w ⟧T) B≡ 
  ∙ sym (dcong₂ Πsem (sym A≡) ([]-helper ⟦ B ⟧T ⟦ δ ⟧w A≡))
  where A≡ = A [ δ ]w≡
        B≡ = B [ δ ↑ _ ]w≡
El' A [ δ ]w≡ = refl

_[_]wtm≡ : ∀ {A} (M : Tm Γ A) (δ : Wk Δ Γ) 
         → ⟦ M [ δ ]wtm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧w
_[_]wv : ∀ {A} → Var Γ A → (δ : Wk Δ Γ) → Var Δ (A ∘ ⟦ δ ⟧w)
_[_]wv≡ : ∀ {A} (x : Var Γ A) (δ : Wk Δ Γ) 
        → ⟦ x [ δ ]wv ⟧v ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧w

x    [ wk    ]wv = vs x
vz   [ δ ↑ A ]wv = subst (Var _) (cong (_∘ semwk _) (A [ δ ]w≡)) 
                         (vz {A = A [ δ ]w})
vs x [ δ ↑ A ]wv = vs (x [ δ ]wv)

x [ wk ]wv≡ = refl
vz [ δ ↑ A ]wv≡ 
  = sym lift ∙ []v-helper (A [ δ ]w≡)
  where 
    lift = subst-application′ (Var _)
                             {y = vz {A = A [ δ ]w}} 
                             (λ _ → ⟦_⟧v)
                             (cong  (_∘ semwk _) (A [ δ ]w≡))
vs x [ δ ↑ A ]wv≡ = cong (_∘ proj₁) (x [ δ ]wv≡)

var x [ δ ]wtm = var (x [ δ ]wv)
app {B = B} M N [ δ ]wtm 
  = subst (λ x → (Tm _ (λ ρ → B (⟦ δ ⟧w ρ , x ρ)))) 
          (N [ δ ]wtm≡) (app (M [ δ ]wtm) (N [ δ ]wtm))
lam {A = A} {B = B} M [ δ ]wtm 
  = subst (Tm _) (Πsem≡ refl A≡ (from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧w A≡))) 
          (lam (M [ δ ↑ _ ]wtm))
  where
    A≡ = A [ δ ]w≡

var x [ δ ]wtm≡ = x [ δ ]wv≡
app {A = A} {B = B} M N [ δ ]wtm≡ 
  = sym lift-subst
  ∙ dcong-app (cong appsem (M [ δ ]wtm≡)) (N [ δ ]wtm≡)
  where lift-subst = subst-application′ (λ x → Tm _ (λ ρ → B (⟦ δ ⟧w ρ , x ρ)))
                                        (λ _ → ⟦_⟧tm) (N [ δ ]wtm≡)
lam {A = A} {B = B} M [ δ ]wtm≡ 
  = sym lift 
  ∙ cong (subst (SemVal _) coe-eq) 
         (cong (λ M′ ρ → M′ ∘ (ρ ,_)) (M [ δ ↑ _ ]wtm≡)) 
  ∙ []tm-helper ⟦ δ ⟧w ⟦ M ⟧tm A≡ B≡
  where A≡ = A [ δ ]w≡
        B≡ = from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧w A≡)
        coe-eq = Πsem≡ refl A≡ B≡
        lift = subst-application′ (Tm _) (λ _ → ⟦_⟧tm) coe-eq

{-# REWRITE _[_]w≡ _[_]wv≡ _[_]wtm≡ #-}

data Sub : Ctx → Ctx → Set

⟦_⟧s : Sub Δ Γ → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c
_[_]s  : Ty Γ → Sub Δ Γ → Ty Δ
_[_]s≡ : ∀ A (δ : Sub Δ Γ) → ⟦ A [ δ ]s ⟧T ≡ ⟦ A ⟧T ∘ ⟦ δ ⟧s

data Sub where
  <_> : Tm Γ ⟦ A ⟧T → Sub Γ (Γ , A)
  _↑_ : ∀ (δ : Sub Γ Δ) A → Sub (Γ , A [ δ ]s) (Δ , A)

⟦ < M > ⟧s = sem< ⟦ M ⟧tm >
⟦ δ ↑ A ⟧s (ρ , x) 
  = (⟦ δ ⟧s ↑s ⟦ A ⟧T) (ρ , subst (λ A[] → El (A[] ρ)) ((A [ δ ]s≡)) x) 

_[_]stm  : ∀ {Γ A} → Tm Γ A → (δ : Sub Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧s)

⊥' [ δ ]s = ⊥'
Π' A B [ δ ]s = Π' (A [ δ ]s) (B [ δ ↑ A ]s)
El' A [ δ ]s = El' (A [ δ ]stm) 

⊥' [ δ ]s≡ = refl
Π' A B [ δ ]s≡ 
  = cong (Πsem ⟦ A [ δ ]s ⟧T) B≡ 
  ∙ sym (dcong₂ Πsem (sym A≡) ([]-helper ⟦ B ⟧T ⟦ δ ⟧s A≡))
  where A≡ = A [ δ ]s≡
        B≡ = B [ δ ↑ _ ]s≡
El' A [ δ ]s≡ = refl

_[_]stm≡ : ∀ {A} (M : Tm Γ A) (δ : Sub Δ Γ) 
         → ⟦ M [ δ ]stm ⟧tm ≡ ⟦ M ⟧tm ∘ ⟦ δ ⟧s
_[_]sv  : ∀ {A} → Var Γ A → (δ : Sub Δ Γ) → Tm Δ (A ∘ ⟦ δ ⟧s)
_[_]sv≡ : ∀ {A} (x : Var Γ A) (δ : Sub Δ Γ) 
       → ⟦ x [ δ ]sv ⟧tm ≡ ⟦ x ⟧v ∘ ⟦ δ ⟧s

vz   [ < M > ]sv = M
vs x [ < M > ]sv = var x 
vz   [ δ ↑ A ]sv = var (subst (Var _) (cong (_∘ semwk _) (A [ δ ]s≡)) vz)
vs x [ δ ↑ A ]sv = x [ δ ]sv [ wk ]wtm

vz [ < M > ]sv≡ = refl
vs x [ < M > ]sv≡ = refl
vz [ δ ↑ A ]sv≡ = sym lift ∙ []v-helper (A [ δ ]s≡)
  where
    lift = subst-application′ (Var _)
                             {y = vz {A = A [ δ ]s}} 
                             (λ _ → ⟦_⟧v)
                             (cong  (_∘ semwk _) (A [ δ ]s≡))
vs x [ δ ↑ A ]sv≡ = cong (_∘ semwk _) (x [ δ ]sv≡)

var x [ δ ]stm = x [ δ ]sv
app {B = B} M N [ δ ]stm 
  = subst (λ x → (Tm _ (λ ρ → B (⟦ δ ⟧s ρ , x ρ)))) 
          (N [ δ ]stm≡) (app (M [ δ ]stm) (N [ δ ]stm))
lam {A = A} {B = B} M [ δ ]stm 
  = subst (Tm _) (Πsem≡ refl A≡ (from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧s A≡))) 
          (lam (M [ δ ↑ _ ]stm))
  where
    A≡ = A [ δ ]s≡

var x [ δ ]stm≡ = x [ δ ]sv≡
app {A = A} {B = B} M N [ δ ]stm≡ 
  = sym lift-subst
  ∙ dcong-app (cong appsem (M [ δ ]stm≡)) (N [ δ ]stm≡)
  where lift-subst = subst-application′ (λ x → Tm _ (λ ρ → B (⟦ δ ⟧s ρ , x ρ)))
                                        (λ _ → ⟦_⟧tm) (N [ δ ]stm≡)
lam {A = A} {B = B} M [ δ ]stm≡ 
  = sym lift 
  ∙ cong (subst (SemVal _) coe-eq) 
         (cong (λ M′ ρ → M′ ∘ (ρ ,_)) (M [ δ ↑ _ ]stm≡)) 
  ∙ []tm-helper ⟦ δ ⟧s ⟦ M ⟧tm A≡ B≡
  where A≡ = A [ δ ]s≡
        B≡ = from-coe≡⁻¹ _ ([]-helper B ⟦ δ ⟧s A≡)
        coe-eq = Πsem≡ refl A≡ B≡
        lift = subst-application′ (Tm _) (λ _ → ⟦_⟧tm) coe-eq


{-# REWRITE _[_]s≡  _[_]sv≡ _[_]stm≡ #-}

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
           