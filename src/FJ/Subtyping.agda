open import FJ.Syntax

module FJ.Subtyping (CT : ClassTable) where

open ClassTable

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

-- subclass relation
data _<:_ : Type → Type → Set where
  S_Refl  : ∀ {C}
    → C <: C
  S_Trans : ∀ {C D E}
    → C <: D
    → D <: E
    → C <: E
  S_Extends : ∀ {C cn D flds mths}
    → C ≡ Class cn
    → dcls CT ∋ (class cn extends D field* flds method* mths)
    → C <: D

-- subclass lifted to lists of types
data _<:*_ : List Type → List Type → Set where
  S_Z : [] <:* []
  S_S : ∀ {C D Cs Ds} → C <: D → Cs <:* Ds → (C ∷ Cs) <:* (D ∷ Ds)
