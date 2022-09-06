open import FJ.Syntax

module FJ.Subtyping (CT : ClassTable) where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

-- subclass relation
data _<:_ : Class → Class → Set where
  S_Refl  : ∀ {C}
    → C <: C
  S_Trans : ∀ {C D E}
    → C <: D
    → D <: E
    → C <: E
  S_Extends : ∀ {C Cname D fields mths}
    → C ≡ Extend Cname D
    → CT ∋ (class Cname fls fields mts mths)
    → C <: D

data _<:ᵀ_ : Type → Type → Set where
  Ty : ∀ {C D} → C <: D → Ty C <:ᵀ Ty D

-- subclass lifted to lists of types
data _<:*_ : List Type → List Type → Set where
  S_Z : [] <:* []
  S_S : ∀ {C D Cs Ds} → C <:ᵀ D → Cs <:* Ds → (C ∷ Cs) <:* (D ∷ Ds)
