{-# OPTIONS --allow-unsolved-metas #-}
open import FJ.Syntax

module FJ.Subtyping (CT : ClassTable) where

open ClassTable

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; _≟_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂; inspect; [_])
open import Relation.Nullary
  using (¬_; Dec; yes; no)

-- subclass relation
data _<:_ : Type → Type → Set where
  S-Refl  : ∀ {C}
    → C <: C
  -- S-Trans : ∀ {C D E}
  --   → C <: D
  --   → D <: E
  --   → C <: E
  S-Extends : ∀ {C cn D flds mths E}
    → C ≡ Class cn
    → declOf cn (dcls CT) ≡ just (class cn extends D field* flds method* mths , refl)
    -- → dcls CT ∋ (class cn extends D field* flds method* mths)
    → D <: E
    → C <: E

S-Trans : ∀ {C D E} → C <: D → D <: E → C <: E
S-Trans S-Refl D<:E = D<:E
S-Trans (S-Extends C≡ dcls∋ C<:D) D<:E = S-Extends C≡ dcls∋ (S-Trans C<:D D<:E)


lemma-cdd1 : ∀ {C D D′} → ¬ (C <: D) → (D′ <: D) → ¬ (C <: D′)
lemma-cdd1 ¬C<:D D′<:D C<:D′ = ¬C<:D (S-Trans C<:D′ D′<:D)

lemma-cdd2 : ∀ {C D D′} → ¬ (D <: C) → (D′ <: D) → ¬ (D′ <: C)
lemma-cdd2 ¬D<:C S-Refl D′<:C = ¬D<:C D′<:C
lemma-cdd2 ¬D<:C (S-Extends x x₁ D′<:D) D′<:C = {!!}

-- subclass lifted to lists of types
data _<:*_ : List Type → List Type → Set where
  S-Z : [] <:* []
  S-S : ∀ {C D Cs Ds} → C <: D → Cs <:* Ds → (C ∷ Cs) <:* (D ∷ Ds)

s-refl* : ∀ {Ts : List Type} → Ts <:* Ts
s-refl* {[]} = S-Z
s-refl* {T ∷ Ts} = S-S S-Refl s-refl*

s-trans* : ∀ {Ts Ts′ Ts″} → Ts <:* Ts′ → Ts′ <:* Ts″ → Ts <:* Ts″
s-trans* S-Z S-Z = S-Z
s-trans* (S-S T<:T′ Ts<:*Ts′) (S-S T′<:T″ Ts′<:*Ts″) = S-S (S-Trans T<:T′ T′<:T″) (s-trans* Ts<:*Ts′ Ts′<:*Ts″)

-- decidable subtyping (needed for preservation)

¬object<:class : ∀ {cn} → ¬ Object <: Class cn
¬object<:class (S-Extends () dcls∋ o<:cn)

class<:object : ∀ {cn} → Dec (Class cn <: Object)
class<:object {cn} with height CT (Class cn)
... | zero = no {!!}
... | suc n = yes {!!}
  where
    proof-of-cn<:object : ℕ → (T : Type) → T <: Object
    proof-of-cn<:object zero T = {!!}
    proof-of-cn<:object (suc n) Object = S-Refl
    proof-of-cn<:object (suc n) (Class cn)
      with  declOf cn (dcls CT) | inspect (declOf cn) (dcls CT)
    ... | nothing | [ eq ] = {!!}
    ... | just (class name extends exts field* flds method* mths , refl) | [ eq ] =
      S-Extends {D = exts}{flds = flds}{mths = mths} refl eq (proof-of-cn<:object n exts)

_<:?_ : (S T : Type) → Dec (S <: T)
Object <:? Object = yes S-Refl
Object <:? Class cn = no ¬object<:class
Class cn <:? Object = class<:object
Class cn <:? Class cn₁ with cn ≟ cn₁
... | yes refl = yes S-Refl
... | no  cn≢cn₁ = {!!}

lemma-cd : ∀ {C}{D} → ¬ (D <: C) → C ≢ D
lemma-cd {Object} {Object} ¬C<:D = ⊥-elim (¬C<:D S-Refl)
lemma-cd {Object} {Class x} ¬C<:D = λ()
lemma-cd {Class x} {Object} ¬C<:D = λ()
lemma-cd {Class cn} {Class cn₁} ¬C<:D with cn ≟ cn₁
... | yes refl = ⊥-elim (¬C<:D S-Refl)
... | no  cn≢cn₁ = λ{ refl → ⊥-elim (cn≢cn₁ refl)}

