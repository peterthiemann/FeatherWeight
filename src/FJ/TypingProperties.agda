open import FJ.Syntax

module FJ.TypingProperties (CT : ClassTable) where

open ClassTable

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂; inspect; [_])

open import FJ.Lookup CT
open import FJ.Typing CT

⊢cd⇒⊢method : ∀ {cd}{meth : MethDecl}
  → (m : MethName) → ∀ m∈ → cd OK → declOf m (ClassDecl.mths cd) ≡ just (meth , m∈ , refl)
  → meth OK-IN (Class (ClassDecl.name cd))
⊢cd⇒⊢method {class name extends exts field* flds method* mths} {meth} m m∈ (T-Class refl mdecls-ok) declOfm≡ = helper mths m∈ mdecls-ok
  where
    helper : (meths : Methods) (m∈ : meths [ (λ v → m) ]∋ meth) (mdecls-ok : All (_OK-IN Class name) meths) → meth OK-IN Class name
    helper [] () mdecls-ok
    helper (x ∷ meths) (here x₁) (px ∷ mdecls-ok) = px
    helper (x ∷ meths) (there m∈ x₁) (px ∷ mdecls-ok) = helper meths m∈ mdecls-ok

⊢program⇒⊢class : ∀ {cd}
  → (cn : ClassName) → ∀ cd∈ → CLASSTABLE CT OK → declOf cn (dcls CT) ≡ just (cd , cd∈ , refl)
  → cd OK
⊢program⇒⊢class {cd} cn cd∈ ⊢program declOfcn≡ = helper (dcls CT) cd∈ ⊢program
  where
    helper : (cc : ClassContext) (cd∈ : cc [ (λ v → cn) ]∋ cd) (cds-ok : All _OK cc) → cd OK
    helper [] () cds-ok
    helper (x ∷ cc) (here x₁) (px ∷ cds-ok) = px
    helper (x ∷ cc) (there cd∈ x₁) (px ∷ cds-ok) = helper cc cd∈ cds-ok
