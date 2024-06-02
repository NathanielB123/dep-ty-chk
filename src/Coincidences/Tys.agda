{-# OPTIONS --rewriting #-}

open import Coincidences.Syntax
open import Coincidences.Sub

module Coincidences.Tys where

data Tys : Ctx → Set
_++_ : ∀ Γ → Tys Γ → Ctx

data Tys where
  ε   : Tys Γ
  _,_ : ∀ Δ → Ty (Γ ++ Δ) → Tys Γ

Γ ++ ε       = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

_[_]tys : Tys Γ → MSub Δ Γ → Tys Δ
_↑↑_ : ∀ (δ : MSub Δ Γ) Γ′ → MSub (Δ ++ (Γ′ [ δ ]tys)) (Γ ++ Γ′)

ε        [ δ ]tys = ε
(Γ′ , A) [ δ ]tys = (Γ′ [ δ ]tys) , (A [ δ ↑↑ Γ′ ])
      
δ ↑↑ ε = δ     
δ ↑↑ (Γ′ , A) = (δ ↑↑ Γ′) ↑m A 
