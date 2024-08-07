{-# OPTIONS --prop --show-irrelevant --rewriting #-}
--local-confluence-check -- Confluence checking here ICEs Agda 2.7.0, welp

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys

-- Renamings + parallel substitutions
module Coincidences.Substitutions.Parallel.RenSub where

open import Coincidences.Substitutions.Parallel.Common public
open import Coincidences.Substitutions.Parallel.Abstract 
  Var ⟦_⟧v vz refl (λ _ → vs) (λ _ _ → refl) var (λ _ → refl)
  renaming (Objects to Vars; ⟦_⟧os to ⟦_⟧vs; _↑os_ to _↑vs_; _↑os≡_ to _↑vs≡_
  ; wkos to wkvars; wkos≡ to wkvars≡
  ; _[_] to _[_]r; _[_]≡ to _[_]r≡
  ; _[_]tm to _[_]rtm; _[_]tm≡ to _[_]rtm≡
  ; _[_]v to _[_]rv; _[_]v≡ to _[_]rv≡
  ) public
{-# REWRITE _[_]r≡ _[_]rv≡ _[_]rtm≡ wkvars≡ #-}

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

wk : Vars (Γ , A) Γ
wk = wkvars _ (id-ren _)

open import Coincidences.Substitutions.Parallel.Abstract 
  Tm ⟦_⟧tm (var vz) refl (λ A → _[ wk ]rtm) (λ _ _ → refl) 
  id (λ _ → refl)
  renaming (Objects to Tms; ⟦_⟧os to ⟦_⟧tms;  _↑os_ to _↑ts_; _↑os≡_ to _↑ts≡_
  ; wkos to wktms; wkos≡ to wktms≡
  )
  public
{-# REWRITE _[_]≡ _[_]v≡ _[_]tm≡ wktms≡ #-}

ren-to-sub : Vars Δ Γ → Tms Δ Γ
ren-to-sub≡ : ∀ (δ : Vars Δ Γ) → ⟦ ren-to-sub δ ⟧tms ≡ ⟦ δ ⟧vs

ren-to-sub ε = Tms.ε
ren-to-sub (_,_ {A = A} δ x) 
  = Tms._,_ (ren-to-sub δ) 
            (var (subst (Var _ ∘ (⟦ A ⟧T ∘_)) (sym (ren-to-sub≡ δ)) x))

ren-to-sub≡ ε = refl
ren-to-sub≡ (_,_ {A = A} δ x) = sym (dcong₂ _,sub_ (sym δ≡) rm-subst)
  where δ≡ = ren-to-sub≡ δ
        rm-subst = subst-application′ (Var _ ∘ (⟦ A ⟧T ∘_)) (λ _ → ⟦_⟧v) 
                                      (sym δ≡)
{-# REWRITE ren-to-sub≡ #-}

id-sub : ∀ Γ → Tms Γ Γ
id-sub Γ = ren-to-sub (id-ren Γ)

<_> : Tm Γ ⟦ A ⟧T → Tms Γ (Γ , A)
< M > = id-sub _ , M
