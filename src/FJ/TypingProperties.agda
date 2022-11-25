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
  → (m∈ : ClassDecl.mths cd [ MethDecl.name ]∋ meth)
  → All (_OK-IN Class (ClassDecl.name cd)) (ClassDecl.mths cd)
  → meth OK-IN (Class (ClassDecl.name cd))
⊢cd⇒⊢method {cd}{meth} m∈ ⊢mdecls = helper (ClassDecl.mths cd) m∈ ⊢mdecls 
  where
    helper : (meths : Methods) (m∈ : meths [ MethDecl.name ]∋ meth) (mdecls-ok : All (_OK-IN Class (ClassDecl.name cd)) meths) → meth OK-IN Class (ClassDecl.name cd)
    helper [] () mdecls-ok
    helper (x ∷ meths) (here x₁) (px ∷ mdecls-ok) = px
    helper (x ∷ meths) (there m∈ x₁) (px ∷ mdecls-ok) = helper meths m∈ mdecls-ok


⊢program⇒⊢class : ∀ {cd}
  → (cd∈ : ClassTable.dcls CT [ ClassDecl.name ]∋ cd)
  → CLASSTABLE CT OK
  → cd OK
⊢program⇒⊢class {cd} cd∈ ⊢program = helper (dcls CT) cd∈ ⊢program
    where
      helper : (cc : ClassContext) (cd∈ : cc [ ClassDecl.name ]∋ cd) (cds-ok : All _OK cc) → cd OK
      helper [] () cds-ok
      helper (x ∷ cc) (here x₁) (px ∷ cds-ok) = px
      helper (x ∷ cc) (there cd∈ x₁) (px ∷ cds-ok) = helper cc cd∈ cds-ok

