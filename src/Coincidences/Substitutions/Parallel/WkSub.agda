{-# OPTIONS --prop --show-irrelevant --rewriting --local-confluence-check #-}

open import Coincidences.Utils
open import Coincidences.Syntax
open import Coincidences.Tys

-- Single weakenings + parallel substitutions
module Coincidences.Substitutions.Parallel.WkSub where

open import Coincidences.Substitutions.Single.Weak public

open import Coincidences.Substitutions.Parallel.Abstract 
  Tm ⟦_⟧tm (var vz) refl (λ A → _[ wk ]wtm) (λ _ _ → refl) 
  id (λ _ → refl)
  renaming (Objects to Tms; ⟦_⟧os to ⟦_⟧tms;  _↑os_ to _↑ts_; _↑os≡_ to _↑ts≡_
  ; wkos to wktms; wkos≡ to wktms≡
  )
  public
{-# REWRITE _[_]≡ _[_]v≡ _[_]tm≡ wktms≡ #-}
