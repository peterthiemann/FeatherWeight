open import FJ.Syntax


open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String)
open import Function using (const)
open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

module FJ.Typing (CT : ClassTable) where

open ClassTable

open import FJ.Lookup (CT)
open import FJ.Subtyping (CT)

-- expression typing

open import Data.List.Relation.Binary.Pointwise

-- data
_⊢*_⦂_ : VarContext → List Exp → List Type → Set
data _⊢_⦂_  Γ : Exp → Type → Set where

  T-Var : ∀ {x}{T}
    → Γ [ Bind.name ]∋ (x ⦂ T)
    -- → declOf{name = Bind.name} x Γ ≡ just ((x ⦂ T) , x∈ , refl)
    → Γ ⊢ Var x ⦂ T

  T-Field : ∀ {e₀}{C₀}{f}{fenv}{T}
    → Γ ⊢ e₀ ⦂ C₀
    → fields C₀ ≡ just fenv
    → fenv [ Bind.name ]∋ (f ⦂ T)
    -- → declOf{name = Bind.name} f (fields C₀) ≡ just (f ⦂ T , f∈ , refl)
    → Γ ⊢ Field e₀ f ⦂ T

  T-Invk : ∀ {e₀}{C₀}{m}{es}{margs}{T}{Ts}
    → Γ ⊢ e₀ ⦂ C₀
    → mtype m C₀ ≡ just (margs , T)
    → Γ ⊢* es ⦂ Ts
    → Ts <:* values margs                      -- backwards?
    → Γ ⊢ Meth e₀ m es ⦂ T

  T-New : ∀ {C} {es} {Ts} {flds}
    → fields C ≡ just flds
    → Γ ⊢* es ⦂ Ts
    → Ts <:* values flds                      -- backwards?
    → Γ ⊢ New C es ⦂ C

  T-UCast : ∀ {C}{D}{e₀}
    → Γ ⊢ e₀ ⦂ D
    → D <: C
    → Γ ⊢ Cast C e₀ ⦂ C

  T-DCast : ∀ {C}{D}{e₀}
    → Γ ⊢ e₀ ⦂ D
    → C <: D
    → C ≢ D
    → Γ ⊢ Cast C e₀ ⦂ C

  T-SCast : ∀ {C}{D}{e₀}
    → Γ ⊢ e₀ ⦂ D
    → ¬ (C <: D)
    → ¬ (D <: C)
    → Γ ⊢ Cast C e₀ ⦂ C

-- beat strict positivity
_⊢*_⦂_ Γ = Pointwise (Γ ⊢_⦂_)

-- data _⊢*_⦂_ Γ where
--   T-Z : Γ ⊢* [] ⦂ []
--   T-S : ∀ {e} {es} {T} {Ts} → Γ ⊢ e ⦂ T → Γ ⊢* es ⦂ Ts → Γ ⊢* (e ∷ es) ⦂ (T ∷ Ts)

-- method typing

data _OK-IN_ : MethDecl → Type → Set where

  T-Method : ∀ {m xs C₀ e₀ E₀ C cn D}
    → (("this" ⦂ C) ∷ xs) ⊢ e₀ ⦂ E₀
    → E₀ <: C₀
    → C ≡ Class cn
    → (∀ {ds D₀} → mtype m D ≡ just (ds , D₀) → (names xs ≡ names ds) × (C₀ ≡ D₀))
    → (method m ⦂ xs ⇒ C₀ return e₀) OK-IN C

-- class typing

data _OK : ClassDecl → Set where

  T-Class : ∀ {C}{cn}{D}{fdecl}{mdecl}
    → C ≡ Class cn
    → All (_OK-IN C) mdecl
    → (class cn extends D field* fdecl method* mdecl) OK

-- program typing

PROGRAM_OK : ClassContext → Set
PROGRAM_OK = All _OK

CLASSTABLE_OK : ClassTable → Set
CLASSTABLE CT OK = PROGRAM (dcls CT) OK
