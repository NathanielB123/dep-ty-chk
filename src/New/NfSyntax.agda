{-# OPTIONS --prop #-}
-- {-# OPTIONS --show-implicit #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Idea: We can define normal forms directly and then define substitutions by
-- first converting into terms, then normalising by evaluation

-- Unfortunately, this doesn't quite mean we can get away with using
-- definitional equality - types must retain explicit substitutions

-- Idea 2: Instead of explicit Coed types, we can embed equations into the terms
-- (fording translation, using the setoid equivalence)

-- Idea 3: Now only types have non-trivial equations relating them, we could
-- define equivalences for all other syntactic structures as recursive functions
-- into Prop. This makes induction a little more awkward, but gives us more
-- definitional equalities.
-- Being able to induct on an equivalence with just one match can also be
-- recovered by adding a view.

-- NEW IDEA!!
-- We would like type equality to be syntactic, but this is hard to combine with
-- having explicit substitutions
-- Recursive type substitutions are non-terminating if they call term 
-- substitution
-- BUT, what if we just made El M [ δ ] a constructor?
-- i.e. type substitutions compute on U and on Π - only get blocked on El
-- We could then recover syntactic equality by removing ordinary El
-- The main problem here is having first-class term-level Π types would be 
-- trickier

-- El M [ δ ◂ σ ] ≈T El (M [ δ ]) [ σ ]

-- Note we will need commuting rules for type substitutions. We *could* only add
-- them for El (or even just Subs) though!

module New.NfSyntax where

-- Utils
data ⊤ : Prop where tt : ⊤
  
data ⊥ : Prop where

record _∧_ (P Q : Prop) : Prop where
  constructor _,_
  eta-equality
  field
    proj₁ : P
    proj₂ : Q
open _∧_

data Squash (P : Set) : Prop where
  sq : P → Squash P

infix 50 _[_]
infix 40 _,_
infix 0 _∧_

data Ctx  : Set
data Ty   : Ctx → Set
data Var  : ∀ Γ → Ty Γ → Set
data Ne   : ∀ Γ → Ty Γ → Set
data Nf   : ∀ Γ → Ty Γ → Set
data Sub  : Ctx → Ctx → Set

data _~T_ : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Set

_≈C_  : Ctx → Ctx → Prop
_≈T_  : ∀ {Γ₁ Γ₂} → Ty Γ₁ → Ty Γ₂ → Prop
_≈v_  : ∀ {Γ₁ Γ₂ A₁ A₂} → Var Γ₁ A₁ → Var Γ₂ A₂ → Prop
_≈ne_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Ne Γ₁ A₁ → Ne Γ₂ A₂ → Prop
_≈nf_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Nf Γ₁ A₁ → Nf Γ₂ A₂ → Prop
_≈s_  : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Sub Γ₁ Δ₁ → Sub Γ₂ Δ₂ → Prop

data Ctx where
  ε   : Ctx 
  _,_ : ∀ Γ → Ty Γ → Ctx

data Ty where
  U  : ∀ {Γ} → Ty Γ
  El : ∀ {Γ} → Nf Γ U → Ty Γ
  Π  : ∀ {Γ} A → Ty (Γ , A) → Ty Γ

  _[_] : ∀ {Γ Δ} → Ty Γ → Sub Δ Γ → Ty Δ

-- This does not work! We need separate Sub and CoedSub...
-- I'm honestly confused right now how it is ok to lift all coes to the
-- outermost level. This is possible with 'Var's and 'Sub's, but not 'app' or
-- 'lam' (I think) and I do not know why
data Sub where
  wk  : ∀ {Γ A Γ,A} → Γ , A ≈C Γ,A → Sub Γ,A Γ
  sub : ∀ {Γ A Γ,A} → Nf Γ A → Γ , A ≈C Γ,A → Sub Γ Γ,A
  _↑_ : ∀ {Γ Δ} δ → ∀ A → Sub (Γ , A [ δ ]) (Δ , A)

wk𝕀 : ∀ {Γ A} → Sub (Γ , A) Γ
<_> : ∀ {Γ A} → Nf Γ A → Sub Γ (Γ , A) 

-- Best justification so far for Coed is Var I think, as we need a coercion in
-- both cases, but if we lifted it out then we would only have a single coercion
-- even in the case of non-zero variables
--
-- We could always insert a coercion inside the var constructor...
data Var where
  vz : ∀ {Γ A} → Var (Γ , A) (A [ wk𝕀 ])
  vs : ∀ {Γ A B} → Var Γ B → Var (Γ , A) (B [ wk𝕀 ])

data Ne where
  var : ∀ {Γ A} → Var Γ A → Ne Γ A
  app : ∀ {Γ A B B<N>} → Ne Γ (Π A B) → ∀ N 
      → B [ < N > ] ≈T B<N> → Ne Γ B<N>

data Nf where
  ne  : ∀ {Γ A} → Ne Γ A → Nf Γ A
  lam : ∀ {Γ A B} {ΠAB : Ty Γ} → (M : Nf (Γ , A) B) 
      → Π A B ≈T ΠAB → Nf Γ ΠAB

ε ≈C ε = ⊤
(Γ , A) ≈C (Δ , B) = Γ ≈C Δ ∧ A ≈T B
_ ≈C _ = ⊥

data _~T_ where
  U : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → U {Γ₁} ~T U {Γ₂}
  -- ...

Γ₁ ≈T Γ₂ = Squash (Γ₁ ~T Γ₂)

-- We could create a view that lets us induct of the prop equalities without
-- having to match twice!

vz {A = A₁} ≈v vz {A = A₂} = A₁ ≈T A₂
vs x ≈v vs y = x ≈v y -- Might need to add evidence of type equality here
_ ≈v _ = ⊥

var x ≈ne var y = x ≈v y
app M₁ N₁ _ ≈ne app M₂ N₂ _ = M₁ ≈ne M₂ ∧ N₁ ≈nf N₂
_ ≈ne _ = ⊥

ne M₁ ≈nf ne M₂ = M₁ ≈ne M₂
lam M₁ _ ≈nf lam M₂ _ = M₁ ≈nf M₂
_ ≈nf _ = ⊥

data _~ne_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Ne Γ₁ A₁ → Ne Γ₂ A₂ → Set
data _~nf_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Nf Γ₁ A₁ → Nf Γ₂ A₂ → Set

data _~ne_ where
  var : ∀ {Γ₁ Γ₂ A₁ A₂} {x : Var Γ₁ A₁} {y : Var Γ₂ A₂} 
     → x ≈v y → var x ~ne var y
  app : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂} 
          {M₁ : Ne Γ₁ (Π A₁ B₁)} {M₂ : Ne Γ₂ (Π A₂ B₂)} {N₁ N₂} 
     → M₁ ~ne M₂ → N₁ ~nf N₂ 
     → ∀ {B<N>₁ B<N>₂} (p : B₁ [ < N₁ > ] ≈T B<N>₁) (q : B₂ [ < N₂ > ] ≈T B<N>₂)
     → app M₁ N₁ p ~ne app M₂ N₂ q

data _~nf_ where
  ne : ∀ {Γ₁ Γ₂ A₁ A₂} {M₁ : Ne Γ₁ A₁} {M₂ : Ne Γ₂ A₂} 
     → M₁ ~ne M₂ → ne M₁ ~nf ne M₂
  lam : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂ M₁ M₂} 
      → M₁ ~nf M₂ → ∀ {ΠAB₁ ΠAB₂} (p : Π A₁ B₁ ≈T ΠAB₁) (q : Π A₂ B₂ ≈T ΠAB₂) 
      → lam M₁ p ~nf lam M₂ q

reify-nf : ∀ {Γ₁ Γ₂ A₁ A₂} (M₁ : Nf Γ₁ A₁) (M₂ : Nf Γ₂ A₂)
         → M₁ ≈nf M₂ → M₁ ~nf M₂ 
reify-ne : ∀ {Γ₁ Γ₂ A₁ A₂} (M₁ : Ne Γ₁ A₁) (M₂ : Ne Γ₂ A₂)
         → M₁ ≈ne M₂ → M₁ ~ne M₂

reify-nf (ne M₁) (ne M₂) M = ne (reify-ne M₁ M₂ M)
reify-nf (lam M₁ p₁) (lam M₂ p₂) M = lam (reify-nf M₁ M₂ M) p₁ p₂

reify-ne (var x) (var y) p = {!!}
reify-ne (app M₁ N₁ p₁) (app M₂ N₂ p₂) (M , N) 
  = app (reify-ne M₁ M₂ M) (reify-nf N₁ N₂ N) p₁ p₂

_∙T_ : ∀ {Γ₁ Γ₂ Γ₃} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {A₃ : Ty Γ₃} 
    → A₁ ≈T A₂ → A₂ ≈T A₃ → A₁ ≈T A₃ 
_∙C_ : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ≈C Γ₂ → Γ₂ ≈C Γ₃ → Γ₁ ≈C Γ₃
symT : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ → A₂ ≈T A₁ 
symC : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → Γ₂ ≈C Γ₁

coe-T : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → Ty Γ₁ → Ty Γ₂
coe-nf : ∀ {Γ₁ Γ₂ A₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ → Nf Γ₁ A₁ → Nf Γ₂ A₂ 

Π≈ : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} {B₁ B₂} 
   → B₁ ≈T B₂ → Π A₁ B₁ ≈T Π A₂ B₂ 

U≈ : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → U {Γ₁} ≈T U {Γ₂}

coh-T : ∀ {Γ₁ Γ₂} (Γ : Γ₁ ≈C Γ₂) A → coe-T Γ A ≈T A

coe-T Γ U = U
coe-T Γ (El M) = El (coe-nf (U≈ Γ) M)
coe-T Γ (Π A B) = Π (coe-T Γ A) (coe-T (Γ , symT (coh-T Γ _)) B)
coe-T Γ (A [ δ ]) = {!   !}

coh-T Γ U = U≈ (symC Γ)
coh-T Γ (El M) = {!   !}
coh-T Γ (Π A B) = Π≈ (coh-T (Γ , symT (coh-T Γ A)) B)
coh-T Γ (A [ x ]) = {!   !}

infixr 6 _∙T_

≈T↑≈C : ∀ {Γ₁ Γ₂} {A₁ : Ty Γ₁} {A₂ : Ty Γ₂} → A₁ ≈T A₂ → Γ₁ ≈C Γ₂

coe-nf p (lam M q) 
  = lam (coe-nf (symT (coh-T (≈T↑≈C p , symT (coh-T (≈T↑≈C p) _)) _)) M) 
        (Π≈ (coh-T _ _) ∙T q ∙T p)
coe-nf p (ne M) = {!!}

≈nf↑≈C : ∀ {Γ₁ Γ₂ A₁ A₂} (M₁ : Nf Γ₁ A₁) (M₂ : Nf Γ₂ A₂)
       → M₁ ≈nf M₂ → Γ₁ ≈C Γ₂

≈nf↑≈T : ∀ {Γ₁ Γ₂ A₁ A₂} (M₁ : Nf Γ₁ A₁) (M₂ : Nf Γ₂ A₂)
       → M₁ ≈nf M₂ → A₁ ≈T A₂
≈nf↑≈T (ne x) (ne x₁) p = {!   !}
≈nf↑≈T (lam M₁ q) (lam M₂ r) p = symT q ∙T Π≈ (≈nf↑≈T M₁ M₂ p) ∙T r



nonempty : Ctx → Prop
nonempty (_ , _) = ⊤
nonempty ε = ⊥

tail : ∀ Γ → nonempty Γ → Ctx
tail (Γ , _) _ = Γ

head : ∀ Γ (p : nonempty Γ) → Ty (tail Γ p)
head (Γ , A) _ = A

nonempty≈ : ∀ {Γ₁ Γ₂} → Γ₁ ≈C Γ₂ → nonempty Γ₁ → nonempty Γ₂
nonempty≈ {_ , _} {_ , _} _ _ = tt

,-inj₁ : ∀ {Γ₁ Γ₂ A₁} (p : Γ₁ , A₁ ≈C Γ₂) → Γ₁ ≈C tail Γ₂ (nonempty≈ p tt)

,-inj₂ : ∀ {Γ₁ Γ₂ A₁} (p : Γ₁ , A₁ ≈C Γ₂) → A₁ ≈T head Γ₂ (nonempty≈ p tt)

