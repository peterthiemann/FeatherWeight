open import FJ.Syntax

module FJ.Preservation (CT : ClassTable) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; lookup; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product
open import Data.String using (String; _≟_)
open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

open import FJ.Lookup (CT)
open import FJ.Subtyping (CT)
open import FJ.Reduction (CT)
open import FJ.Typing (CT)

subject-reduction* : ∀ {Γ}{es es′}{Ts}
  → Γ ⊢* es ⦂ Ts
  → es ⟶′ es′
  → ∃[ Ts′ ] (Ts′ <:* Ts × Γ ⊢* es′ ⦂ Ts′)

subject-reduction : ∀ {Γ}{e e′}{T}
  → Γ ⊢ e ⦂ T
  → e ⟶ e′
  → ∃[ T′ ] (T′ <: T × Γ ⊢ e′ ⦂ T′)

subject-reduction (T-Field ⊢e ⊢C₀ x₁) (R-Field len≡ x) = {!!}
subject-reduction (T-Invk ⊢e ⊢C₀ x₁ x₂ x₃) (R-Invk x len≡) = {!!}
subject-reduction (T-UCast {C}{D}{e₀} (T-New ⊢C fields≡ ⊢*es Ts<:*) D<:C ⊢C′) (R-Cast D<:C′) =
  D , D<:C , T-New ⊢C fields≡ ⊢*es Ts<:*
subject-reduction (T-DCast {C}{D}{e₀} (T-New {C₁} ⊢C₁ fields≡ ⊢*es Ts<:*) C<:D C≢D ⊢C) (R-Cast D<:C) =
  C₁ , D<:C , (T-New ⊢C₁ fields≡ ⊢*es Ts<:*)
subject-reduction (T-SCast {C}{D}{e₀} (T-New {C₁} ⊢C₁ fields≡ ⊢*es Ts<:*) ¬C<:D ¬D<:C ⊢C) (R-Cast D<:C) =
  ⊥-elim (¬D<:C D<:C)
subject-reduction (T-Field {e₀}{C₀}{f}{T} ⊢e ⊢C₀ decl-f≡) (RC-Field e⟶e′)
  with subject-reduction ⊢e e⟶e′
... | C₀′ , C₀′<:C₀ , ⊢e′ = T , S-Refl , T-Field ⊢e′ {!!} {!!}
subject-reduction (T-Invk {e₀}{C₀}{m}{es}{margs}{T}{Ts} ⊢e₀ ⊢C₀ mtype≡ ⊢*es Ts<:*) (RC-Invk-Recv e⟶e′)
  with subject-reduction ⊢e₀ e⟶e′
... | C₀′ , C₀′<:C₀ , ⊢e₀′ = T , S-Refl , T-Invk ⊢e₀′ {!!} {!mtype≡!} ⊢*es Ts<:*
subject-reduction (T-Invk {e₀}{C₀}{m}{es}{margs}{T}{Ts} ⊢e ⊢C₀ mtype≡ ⊢*es Ts<:*) (RC-Invk-Arg es⟶′es′)
  with subject-reduction* ⊢*es es⟶′es′
... | Ts′ , Ts′<:* , ⊢*es′ = T , S-Refl , T-Invk ⊢e ⊢C₀ mtype≡ ⊢*es′ (s-trans* Ts′<:* Ts<:*)
subject-reduction (T-New {C} {es} {Ts} {flds} ⊢C fields≡ ⊢*es Ts<:*) (RC-New-Arg es⟶′es′)
  with subject-reduction* ⊢*es es⟶′es′
... | Ts′ , Ts′<:* , ⊢*es′ = C , S-Refl , T-New ⊢C fields≡ ⊢*es′ (s-trans* Ts′<:* Ts<:*)
subject-reduction (T-UCast {C}{D}{e₀} ⊢e D<:C ⊢C) (RC-Cast e⟶e′)
  with subject-reduction ⊢e e⟶e′
... | D′ , D′<:D , ⊢e′ = C , S-Refl , T-UCast ⊢e′ (S-Trans D′<:D D<:C) ⊢C
subject-reduction (T-DCast {C}{D}{e₀} ⊢e C<:D C≢D ⊢C) (RC-Cast e⟶e′)
  with subject-reduction ⊢e e⟶e′
... | D′ , D′<:D , ⊢e′
  with D′ [ {!!} ]<:? C
... | yes D′<:C = C , S-Refl , T-UCast ⊢e′ D′<:C ⊢C
... | no ¬D′<:C
  with C [ ⊢C ]<:? D′
... | yes C<:D′ = C , S-Refl , T-DCast ⊢e′ C<:D′ (lemma-cd ¬D′<:C) ⊢C
... | no ¬C<:D′ = C , S-Refl , T-SCast ⊢e′ ¬C<:D′ ¬D′<:C ⊢C
subject-reduction (T-SCast {C}{D}{e₀} ⊢e ¬C<:D ¬D<:C ⊢C) (RC-Cast e⟶e′)
  with subject-reduction ⊢e e⟶e′
... | D′ , D′<:D , ⊢e′ with lemma-cdd2 {!!} ¬D<:C D′<:D
... | no ¬D′<:C =
  C , S-Refl , T-SCast ⊢e′ (lemma-cdd1 ¬C<:D D′<:D) ¬D′<:C ⊢C
... | yes D′<:C = C , S-Refl , T-UCast ⊢e′ D′<:C ⊢C

subject-reduction* (T-S {e} {es} {T} {Ts} ⊢e ⊢*es) (RC-here e⟶e′)
  with subject-reduction ⊢e e⟶e′
... | T′ , T′<: , ⊢e′ = T′ ∷ Ts , (S-S T′<: s-refl*) , T-S ⊢e′ ⊢*es
subject-reduction* (T-S {e} {es} {T} {Ts} ⊢e ⊢*es) (RC-there es⟶′es′)
  with subject-reduction* ⊢*es es⟶′es′
... | Ts′ , Ts′<:* , ⊢*es′ = (T ∷ Ts′) , S-S S-Refl Ts′<:* , T-S ⊢e ⊢*es′
