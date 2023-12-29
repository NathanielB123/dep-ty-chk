open import 1Lab.1Lab.Type using (Type)
open import 1Lab.1Lab.Path using (_≡_; subst; ap)
open import 1Lab.1Lab.HLevel using (is-set)

open import DepTyChk.CubicalUtils using (_≡[_]≡_)
open import DepTyChk.Utils using (_∘_)

-- Abstract syntax

module DepTyChk.Abstract where

record Syntax : Type₁ where

  infix 5 _∘ₛ_
  infix 5 _,ₛ_
  infix 5 _,_
  infixr 6 _[_]T
  infixr 6 _[_]t

  field
    Ctx : Type
    Ty  : Ctx → Type
    Tm  : (Γ : Ctx) → Ty Γ → Type
    Sub : Ctx → Ctx → Type

    -- Ctx
    ε     : Ctx
    _,_   : (Γ : Ctx) → Ty Γ → Ctx
    -- Ty
    U     : ∀ {Γ}   → Ty Γ
    El    : ∀ {Γ}   → Tm Γ U → Ty Γ
    Π     : ∀ {Γ}   → (A : Ty Γ) → Ty (Γ , A) → Ty Γ
    _[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    -- Sub
    εₛ    : ∀ {Γ}     → Sub Γ ε
    _,ₛ_  : ∀ {Γ Δ A} → (δ : Sub Γ Δ) → Tm Γ (A [ δ ]T) → Sub Γ (Δ , A)
    idₛ   : ∀ {Γ}     → Sub Γ Γ
    _∘ₛ_  : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
    tail  : ∀ {Γ Δ A} → Sub Γ (Δ , A) → Sub Γ Δ
    -- Tm
    lam   : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
    app   : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ , A) B
    head  : ∀ {Γ Δ A} → (δ : Sub Γ (Δ , A)) → Tm Γ (A [ tail δ ]T)
    _[_]t : ∀ {Γ Δ A} → Tm Δ A → (δ : Sub Γ Δ) → Tm Γ (A [ δ ]T)

    -- Paths
    -- Ty
    [id]T : ∀ {Γ} {A : Ty Γ} → A [ idₛ ]T ≡ A
    [][]T : ∀ {Γ Δ Σ A} {δ : Sub Δ Σ} {σ : Sub Γ Δ} 
          → A [ δ ]T [ σ ]T ≡ A [ δ ∘ₛ σ ]T
    U[]   : ∀ {Γ Δ} {δ : Sub Γ Δ} → U [ δ ]T ≡ U
    El[]  : ∀ {Γ Δ A} {δ : Sub Γ Δ} 
          → El A [ δ ]T ≡ El (subst (Tm Γ) U[] (A [ δ ]t))
  
  _↑_   : ∀ {Γ Δ} → (δ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , A [ δ ]T) (Δ , A)
  δ ↑ A = (δ ∘ₛ tail idₛ) ,ₛ subst (Tm _) [][]T (head idₛ)
  
  field
    Π[]   : ∀ {Γ Δ A B} {δ : Sub Γ Δ} → Π A B [ δ ]T 
          ≡ Π (A [ δ ]T) (B [ δ ↑ A ]T)
    -- Sub
    idl   : ∀ {Γ Δ} {δ : Sub Γ Δ} → idₛ ∘ₛ δ ≡ δ
    idr   : ∀ {Γ Δ} {δ : Sub Γ Δ} → δ ∘ₛ idₛ ≡ δ
    ass   : ∀ {Γ Δ Σ Ξ} {δ : Sub Σ Ξ} {σ : Sub Δ Σ} {γ : Sub Γ Δ}
          → (δ ∘ₛ σ) ∘ₛ γ ≡ δ ∘ₛ (σ ∘ₛ γ)
    ,∘    : ∀ {Γ Δ Σ A} {δ : Sub Γ Δ} {σ : Sub Σ Γ} {M : Tm Γ (A [ δ ]T)} 
          → (δ ,ₛ M) ∘ₛ σ ≡ (δ ∘ₛ σ) ,ₛ subst (Tm _) [][]T (M [ σ ]t)
    tβ    : ∀ {Γ Δ A} {δ : Sub Γ Δ} {M : Tm Γ (A [ δ ]T)} → tail (δ ,ₛ M) ≡ δ
    ,η    : ∀ {Γ Δ A} {δ : Sub Γ (Δ , A)} → tail δ ,ₛ head δ ≡ δ
    εη    : ∀ {Γ} {δ : Sub Γ ε} → δ ≡ εₛ
    -- Tm
    [id]t : ∀ {Γ A} {M : Tm Γ A} → M [ idₛ ]t ≡[ ap (Tm _) [id]T ]≡ M
    [][]t : ∀ {Γ Δ Σ A} {M : Tm Σ A} {δ : Sub Δ Σ} {σ : Sub Γ Δ}
          → M [ δ ]t [ σ ]t ≡[ ap (Tm _) [][]T ]≡ M [ δ ∘ₛ σ ]t 
    hβ    : ∀ {Γ Δ A} {δ : Sub Γ Δ} {M : Tm Γ (A [ δ ]T)} 
          → head (δ ,ₛ M) ≡[ ap (Tm _ ∘ _[_]T A) tβ ]≡ M
    Πβ    : ∀ {Γ A B} {M : Tm (Γ , A) B} → app (lam M) ≡ M
    Πη    : ∀ {Γ A B} {M : Tm Γ (Π A B)} → lam (app M) ≡ M
    lam[] : ∀ {Γ Δ A B} {δ : Sub Δ Γ} {M : Tm (Γ , A) B} 
          → (lam M) [ δ ]t ≡[ ap (Tm _) Π[] 
          ]≡ lam (M [ δ ↑ A ]t)
    -- Truncation
    squash-Ctx : is-set Ctx
    squash-Ty  : ∀ {Γ} → is-set (Ty Γ)
    squash-Tm  : ∀ {Γ A} → is-set (Tm Γ A)
    squash-Sub : ∀ {Γ Δ} → is-set (Sub Γ Δ)

record Elim : Type₁ where
  
-- record Motives {ℓ₁ ℓ₂ ℓ₃ ℓ₄} : Type (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
record Motives (S : Syntax) : Type₁ where
  open Syntax S public
  field
    Ctxᴹ : Ctx → Type
    Tyᴹ  : ∀ {Γ} → Ctxᴹ Γ → Ty Γ → Type
    Tmᴹ  : ∀ {Γ} {A} (Γᴹ : Ctxᴹ Γ) → Tyᴹ Γᴹ A → Tm Γ A → Type
    Subᴹ : ∀ {Γ Δ} → Ctxᴹ Γ → Ctxᴹ Δ → Sub Γ Δ → Type

record Methods {S} (M : Motives S) : Type where
  open Motives M public
  field
    -- Ctx
    εᴹ   : Ctxᴹ ε
    _,ᴹ_ : ∀ {Γ A} (Γᴹ : Ctxᴹ Γ) → Tyᴹ Γᴹ A → Ctxᴹ (Γ , A)
    -- Ty
    Uᴹ   : ∀ {Γ} {Γᴹ : Ctxᴹ Γ} → Tyᴹ Γᴹ U
    Elᴹ  : ∀ {Γ M} {Γᴹ : Ctxᴹ Γ} → Tmᴹ Γᴹ Uᴹ M → Tyᴹ Γᴹ (El M)
    Πᴹ   : ∀ {Γ} {Γᴹ : Ctxᴹ Γ} {A B} (Aᴹ : Tyᴹ Γᴹ A) → Tyᴹ (Γᴹ ,ᴹ Aᴹ) B 
         → Tyᴹ Γᴹ (Π A B)
    -- We might be able to remove explicit substitutions from the concrete
    -- HIT-based syntax, but we still need to handle this case to give correct
    -- signatures to later methods...
    -- This is quite unfortunate IMO, clearly when matching on the HIT-based
    -- syntax this can be avoided.
    -- I think it should be possible to get around this with an 
    -- inductive-recursive definition, but it is a bit subtle
    -- (We could define an eliminator that is just strong enough to define _[_]T
    -- and then a full eliminator) 
    _[_]Tᴹ : ∀ {Γ Δ A δ} {Γᴹ : Ctxᴹ Γ} {Δᴹ : Ctxᴹ Δ} 
           → Tyᴹ Δᴹ A → Subᴹ Γᴹ Δᴹ δ → Tyᴹ Γᴹ (A [ δ ]T)
    -- Sub
    εₛ   : ∀ {Γ} {Γᴹ : Ctxᴹ Γ} → Subᴹ Γᴹ εᴹ εₛ
    _,ₛ_ : ∀ {Γ Δ A} {δ : Sub Γ Δ} {M : Tm Γ (A [ δ ]T)} {Γᴹ Δᴹ Aᴹ}
         → (δᴹ : Subᴹ Γᴹ Δᴹ δ) → Tmᴹ Γᴹ (Aᴹ [ δᴹ ]Tᴹ) M 
         → Subᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) (δ ,ₛ M) 
    
--     idₛ   : ∀ {Γ}     → Sub Γ Γ
--     _∘ₛ_  : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
--     tail  : ∀ {Γ Δ A} → Sub Γ (Δ , A) → Sub Γ Δ
--     -- Tm
--     lam   : ∀ {Γ A B} → Tm (Γ , A) B → Tm Γ (Π A B)
--     app   : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ , A) B
--     head  : ∀ {Γ Δ A} → (δ : Sub Γ (Δ , A)) → Tm Γ (A [ tail δ ]T)
--     _[_]t : ∀ {Γ Δ A} → Tm Δ A → (δ : Sub Γ Δ) → Tm Γ (A [ δ ]T)
