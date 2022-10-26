open import FJ.Syntax

module FJ.Reduction (CT : ClassTable) where

open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just;nothing)
open import Data.Nat.Properties using (suc-injective)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (_≟_)
open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

open import FJ.Subtyping (CT)
open import FJ.Lookup (CT)

-- substitution

_[_↦_]* : List Exp → VarName → Exp → List Exp
_[_↦_] : Exp → VarName → Exp → Exp
Var y        [ x ↦ e ] with x ≟ y
... | yes x≡y = e
... | no  x≢y = Var y
Field e₀ f   [ x ↦ e ] = Field (e₀ [ x ↦ e ]) f
Meth e₀ m es [ x ↦ e ] = Meth (e₀ [ x ↦ e ]) m (es [ x ↦ e ]*)
New C es     [ x ↦ e ] = New C ( es [ x ↦ e ]*)
Cast C e₀    [ x ↦ e ] = Cast C (e₀ [ x ↦ e ])
If e₀ e₁ e₂  [ x ↦ e ] = If (e₀ [ x ↦ e ]) (e₁ [ x ↦ e ]) (e₂ [ x ↦ e ])

[]           [ x ↦ e ]* = []
(e₀ ∷ es)    [ x ↦ e ]* = e₀ [ x ↦ e ] ∷ es [ x ↦ e ]*

_[_] : Exp → List (Bind VarName Exp) → Exp
e₀ [ [] ]            = e₀
e₀ [ (x ⦂ e) ∷ xes ] = (e₀ [ x ↦ e ]) [ xes ]

-- reduction

zip : ∀ {A B : Set} → List A → List B → List (Bind A B)
zip [] [] = []
zip [] (y ∷ ys) = []
zip (x ∷ xs) [] = []
zip (x ∷ xs) (y ∷ ys) = (x ⦂ y) ∷ zip xs ys

_⤇_ = zip 


data _⟶′_ : List Exp → List Exp → Set 
data _⟶_ : Exp → Exp → Set where

  -- computation

  R-Field : ∀ {C es f}{fenv}{e}
    → fields C ≡ just fenv
    → (names fenv ⤇ es) [ Bind.name ]∋ (f ⦂ e)
    → Field (New C es) f ⟶ e

  R-Invk : ∀ {C es m ds xs e₀}
    → mbody m C ≡ just (xs , e₀)
    → Meth (New C es) m ds ⟶ ((e₀ [ "this" ↦ New C es ]) [ xs ⤇ ds ])

  R-Cast : ∀ {C D es}
    → C <: D
    → Cast D (New C es) ⟶ New C es

  -- congruence

  RC-Field : ∀ {e₀ e₀′ f}
    → e₀ ⟶ e₀′
    → Field e₀ f ⟶ Field e₀′ f

  RC-Invk-Recv : ∀ {e₀ e₀′ m es}
    → e₀ ⟶ e₀′
    → Meth e₀ m es ⟶ Meth e₀′ m es

  RC-Invk-Arg : ∀ {e₀ m es es′}
    → es ⟶′ es′
    → Meth e₀ m es ⟶ Meth e₀ m es′

  RC-New-Arg : ∀ {C es es′}
    → es ⟶′ es′
    → New C es ⟶ New C es′

  RC-Cast : ∀ {C e₀ e₀′}
    → e₀ ⟶ e₀′
    → Cast C e₀ ⟶ Cast C e₀′

data _⟶′_ where

  RC-here : ∀ {eᵢ eᵢ′ es}
    → eᵢ ⟶ eᵢ′
    → (eᵢ ∷ es) ⟶′ (eᵢ′ ∷ es)

  RC-there : ∀ {e es es′}
    → es ⟶′ es′
    → (e ∷ es) ⟶′ (e ∷ es′)
