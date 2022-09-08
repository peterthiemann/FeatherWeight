open import FJ.Syntax


open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
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

data _⊢*_⦂_ (Γ : VarContext) : List Exp → List Type → Set
data _⊢_⦂_ (Γ : VarContext) : Exp → Type → Set where

  T-Var : ∀ {x}{T}
    → declOf x Γ ≡ just (x ⦂ T , refl)
    → Γ ⊢ Var x ⦂ T

  T-Field : ∀ {e₀}{C₀}{f}{T}
    → Γ ⊢ e₀ ⦂ C₀
    → (⊢C₀ : wf (dcls CT) C₀)
    → declOf f (fields ⊢C₀) ≡ just (f ⦂ T , refl)
    → Γ ⊢ Field e₀ f ⦂ T

  T-Invk : ∀ {e₀}{C₀}{m}{es}{margs}{T}{Ts}
    → Γ ⊢ e₀ ⦂ C₀
    → (⊢C₀ : wf (dcls CT) C₀)
    → mtype m ⊢C₀ ≡ just (margs , T)
    → Γ ⊢* es ⦂ Ts
    → Ts <:* bound margs                      -- backwards?
    → Γ ⊢ Meth e₀ m es ⦂ T

  T-New : ∀ {C} {es} {Ts} {flds}
    → (⊢C : wf (dcls CT) C)
    → fields ⊢C ≡ flds
    → Γ ⊢* es ⦂ Ts
    → Ts <:* bound flds                      -- backwards?
    → Γ ⊢ New C es ⦂ C

  T-UCast : ∀ {C}{D}{e₀}
    → Γ ⊢ e₀ ⦂ D
    → D <: C
    → (wfc : wf₀ CT C)
    → Γ ⊢ Cast C e₀ ⦂ C

  T-DCast : ∀ {C}{D}{e₀}
    → Γ ⊢ e₀ ⦂ D
    → C <: D
    → C ≢ D
    → (wfc : wf₀ CT C)
    → Γ ⊢ Cast C e₀ ⦂ C

  T-SCast : ∀ {C}{D}{e₀}
    → Γ ⊢ e₀ ⦂ D
    → ¬ (C <: D)
    → ¬ (D <: C)
    → (wfc : wf₀ CT C)
    → Γ ⊢ Cast C e₀ ⦂ C

-- beat strict positivity
data _⊢*_⦂_ Γ where
  T-Z : Γ ⊢* [] ⦂ []
  T-S : ∀ {e} {es} {T} {Ts} → Γ ⊢ e ⦂ T → Γ ⊢* es ⦂ Ts → Γ ⊢* (e ∷ es) ⦂ (T ∷ Ts)

-- method typing

data _OK-IN_ : MethDecl → Type → Set where

  T-Method : ∀ {m xs C₀ e₀ E₀ C cn D}
    → (xs ▷ ("this" ⦂ C)) ⊢ e₀ ⦂ E₀
    → E₀ <: C₀
    → C ≡ Class cn
    → (⊢*xs : wf* CT xs)
    → (⊢D : wf₀ CT D)
    → (∀ {ds D₀} → mtype m ⊢D ≡ just (ds , D₀) → (bound xs ≡ bound ds) × (C₀ ≡ D₀))
    → (method m ⦂ xs ⇒ C₀ return e₀) OK-IN C

-- class typing

data _OK : ClassDecl → Set where

  T-Class : ∀ {C cn}{D}{fdecl}{mdecl}
    → C ≡ Class cn
    → All (_OK-IN C) (toList mdecl)
    → (class cn extends D field* fdecl method* mdecl) OK

-- program typing

data PROGRAM_OK : ClassContext → Set where

  T-Prog0 : PROGRAM ∅ OK

  T-Prog1 : ∀ {cc cd}
    → PROGRAM cc OK
    → cd OK
    → PROGRAM cc ▷ cd OK

-- typing guarantees wellformedness

preserves-wf-var : ∀ {Γ}{v}{T}
  → wf* CT Γ
  → declOf v Γ ≡ just ((v ⦂ T) , refl)
  → wf₀ CT T
preserves-wf-var {Γ}{v}{T} ⊢Γ declOf≡ = helper ⊢Γ (decl→∋ Γ v (v ⦂ T) refl declOf≡)
  where
    helper : ∀ {Γ} → wf* CT Γ → Γ ∋ (v ⦂ T) → wf₀ CT T
    helper (⊢T , _) here = ⊢T
    helper (_ , ⊢Γ) (there Γ∋ x) = helper ⊢Γ Γ∋

{-
preserves-wf : ∀ {Γ}{e}{T}
  → wf* CT Γ
  → Γ ⊢ e ⦂ T
  → wf₀ CT T
preserves-wf ⊢Γ (T-Var x) = preserves-wf-var ⊢Γ x
preserves-wf ⊢Γ (T-Field ⊢e ⊢C₀ x) = {!!}
preserves-wf ⊢Γ (T-Invk ⊢e ⊢C₀ mtype≡ ⊢*es Ts<:*) = {!!}
preserves-wf ⊢Γ (T-New ⊢C x x₁ x₂) = ⊢C
preserves-wf ⊢Γ (T-UCast {C}{D}{e₀} ⊢e x ⊢C) = ⊢C
preserves-wf ⊢Γ (T-DCast {C}{D}{e₀} ⊢e x x₁ ⊢C) = ⊢C
preserves-wf ⊢Γ (T-SCast {C}{D}{e₀} ⊢e x x₁ ⊢C) = ⊢C
-}
