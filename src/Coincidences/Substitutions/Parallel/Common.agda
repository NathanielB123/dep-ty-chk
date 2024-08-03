{-# OPTIONS --prop --show-irrelevant --rewriting #-}
--local-confluence-check

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys

module Coincidences.Substitutions.Parallel.Common where

infix 100 _⟦_⟧obj

εsem = ⊤

semwk* : ∀ Γ → SemSub ⟦ Γ ⟧c εsem
semwk* ε = id
semwk* (Γ , A) = semwk* Γ ∘ semwk ⟦ A ⟧T

_,sub_ : ∀ {Γ Δ A} (δ : SemSub Δ Γ) → SemVal Δ (A ∘ δ) 
          → SemSub Δ (Γ ,s A) 
(δ ,sub M) ρ = δ ρ , M ρ

Object : Set₁
Object = ∀ Γ → SemTy ⟦ Γ ⟧c → Set

data Objects {O : Object} 
             (i : (∀ {Γ A} → O Γ A → SemVal ⟦ Γ ⟧c A) ) 
             : Ctx → Ctx → Set
_⟦_⟧obj : ∀ {O : Object} (i : ∀ {Γ A} → O Γ A → SemVal ⟦ Γ ⟧c A) 
         → Objects i Δ Γ → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c

data Objects {O} i where
  ε   : Objects i Δ ε
  _,_ : ∀ ρ → O Δ (⟦ A ⟧T ∘ i ⟦ ρ ⟧obj) → Objects i Δ (Γ , A)

i ⟦ ε ⟧obj = semwk* _
i ⟦ ρ , M ⟧obj = i ⟦ ρ ⟧obj ,sub i M

-- Correspond to parallel substitutions
Tms = Objects ⟦_⟧tm

-- Correspond to renamings
Vars = Objects ⟦_⟧v

⟦_⟧tms : Tms Δ Γ → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c
⟦_⟧tms = ⟦_⟧tm ⟦_⟧obj

{-# INLINE ⟦_⟧tms #-}

⟦_⟧vs : Vars Δ Γ → SemSub ⟦ Δ ⟧c ⟦ Γ ⟧c
⟦_⟧vs = ⟦_⟧v ⟦_⟧obj

{-# INLINE ⟦_⟧vs #-}

ren-to-sub : Vars Δ Γ → Tms Δ Γ
ren-to-sub≡ : ∀ (δ : Vars Δ Γ) → ⟦ ren-to-sub δ ⟧tms ≡ ⟦ δ ⟧vs

ren-to-sub ε = ε
ren-to-sub (_,_ {A = A} δ x) 
  = ren-to-sub δ , var (subst (Var _ ∘ (⟦ A ⟧T ∘_)) (sym (ren-to-sub≡ δ)) x)

ren-to-sub≡ ε = refl
ren-to-sub≡ (_,_ {A = A} δ x) = sym (dcong₂ _,sub_ (sym δ≡) rm-subst)
  where δ≡ = ren-to-sub≡ δ
        rm-subst = subst-application′ (Var _ ∘ (⟦ A ⟧T ∘_)) (λ _ → ⟦_⟧v) 
                                      (sym δ≡)

{-# REWRITE ren-to-sub≡ #-}

↑[]-helper : ∀ {Γ Δ} (δ : SemSub Δ Γ) {A} {A[]} (A≡ : A[] ≡ A ∘ δ) 
           → coe (sym (cong₂ SemSub (cong (Δ ,s_) A≡) refl)) (δ ↑s A)
           ≡ (δ ∘ semwk _) 
           ,sub subst (λ A′ → SemVal _ (A′ ∘ semwk A[])) A≡ semvz
↑[]-helper δ refl = refl

[]lam-helper : ∀ {Γ Δ} (δ : SemSub Δ Γ) A {A[]} (A≡ : A[] ≡ A ∘ δ )
             → (λ ρ → subst (λ AB → El (AB (ρ .proj₁))) A≡ (ρ .proj₂))
             ≡  subst (λ A′ → SemVal (Δ ,s _) (A′ ∘ semwk A[])) A≡ proj₂
[]lam-helper δ A refl = refl

[]lam≡-helper : ∀ {Γ Δ} (δ : SemSub Δ Γ) {A B A[] δ↑A} (M : SemVal (Γ ,s A) B) 
                  (p : A[] ≡ A ∘ δ) (q : _ ≡ δ↑A) r
              → subst (SemVal Δ) r (lamsem (subst (SemVal (Δ ,s A[]) ∘ (B ∘_)) q
                      (M ∘ coe (sym (cong₂ SemSub (cong (_,s_ Δ) p) refl)) 
                      (δ ↑s A))))
              ≡ lamsem M ∘ δ
[]lam≡-helper _ _ refl refl refl = refl

vars : ∀ Γ (Γ′ : Tys Γ) → Vars (Γ ++ Γ′) Γ
pick : ∀ A Γ′ → Var (Γ ++ shift A Γ′) (⟦ A ⟧T ∘ ⟦ vars Γ (shift A Γ′) ⟧vs) 
id-ren : ∀ Γ → Vars Γ Γ

id-ren Γ = vars Γ ε

vars≡ : ∀ Γ Γ′ B 
          → ⟦ vars Γ (Γ′ , B) ⟧vs ≡ ⟦ vars Γ Γ′ ⟧vs ∘ semwk ⟦ B ⟧T
id-ren≡ : ∀ Γ → ⟦ id-ren Γ ⟧vs ≡ id

vars ε Γ′ = ε
vars (Γ , A) Γ′ 
  = vars Γ (shift A Γ′) , pick A Γ′

pick A ε 
  = subst (Var _ ∘ (⟦ A ⟧T ∘_)) 
          (sym (vars≡ _ ε A ∙ cong (_∘ semwk _) (id-ren≡ _))) 
          vz
pick A (Γ′ , B) 
  = subst (Var _ ∘ (⟦ A ⟧T ∘_)) (sym (vars≡ _ (shift A Γ′) B)) 
          (vs (pick A Γ′))

vars≡ ε Γ′ B = refl
vars≡ (Γ , A) Γ′ B 
  = sym (dcong₂ _,sub_ (sym Γ≡) rm-coe)
  where Γ≡ = vars≡ Γ (shift A Γ′) B
        rm-coe = subst-application′ (Var (_ , B) ∘ (⟦ A ⟧T ∘_)) (λ _ → ⟦_⟧v) 
                                    (sym Γ≡)

id-ren≡ ε = refl
id-ren≡ (Γ , A) = sym (dcong₂ _,sub_ (sym prf) rm-subst)
  where prf = vars≡ Γ ε A ∙ cong (_∘ semwk _) (id-ren≡ Γ)
        rm-subst = subst-application′ (Var (_ , A) ∘ (⟦ A ⟧T ∘_)) (λ _ → ⟦_⟧v) 
                                      (sym prf)

{-# REWRITE id-ren≡ #-}