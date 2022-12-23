open import FJ.Syntax

module FJ.Experimental (CT : ClassTable) where

open ClassTable

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.String using (String; _≟_)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂; inspect; [_])
open import Relation.Nullary
  using (¬_; Dec; yes; no)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)

open import FJ.Lookup CT
open import FJ.Subtyping CT

fields′ : ∀ {C} → C <: Object → Fields
fields′ S-Refl = []
fields′ (S-Extends {C}{cn}{C′}{flds}{mths}{Object} C≡Class-cn decls∋cn C′<:Obj) =
  fields′ C′<:Obj ++ flds

<:⇒ancestor : ∀ {C} {D} → C <: D → ∃[ i ] ancestor (dcls CT) C i ≡ D
<:⇒ancestor {Object} S-Refl = 0 , refl
<:⇒ancestor {Class _} S-Refl = 0 , refl
<:⇒ancestor {Class cn} (S-Extends {D = C′} refl decl∈₁ C′<:D)
  with <:⇒ancestor C′<:D
... | i , anc-i≡D
  with declOf+ {name = ClassDecl.name} cn (dcls CT) in eq
... | inj₂ decl∉ = ⊥-elim (member-exclusive decl∈₁ decl∉)
... | inj₁ ((class .cn extends exts field* flds method* mths) , decl∈₂ , refl)
  with cc∋-functional decl∈₁ decl∈₂
... | refl , refl , refl
    = suc i , trans (lemma eq) anc-i≡D
  where
    lemma : declOf+ {name = ClassDecl.name} cn (dcls CT) ≡ inj₁ ((class cn extends exts field* flds method* mths) , decl∈₂ , refl)
      → ancestor (dcls CT) (Class cn) (suc i) ≡ ancestor (dcls CT) exts i
    lemma dcl≡ rewrite eq = refl

proposed-lemma-0 : ∀ {C}{D}{fenv-d}
  → C <: D
  → fields D ≡ just fenv-d
  → ∃[ fenv-delta ] (fields C ≡ just (fenv-d ++ fenv-delta))
proposed-lemma-0 {C} {fenv-d = fenv-d} S-Refl fields-d≡ =
   [] , (begin
           fields C
         ≡⟨ fields-d≡ ⟩
           just fenv-d ≡˘⟨ cong just (++-identityʳ fenv-d) ⟩
           just (fenv-d ++ [])
         ∎)
proposed-lemma-0 (S-Extends {C}{cn}{C′}{flds}{mths}{D} C≡Class-cn decls∋cn C′<:D) fields-d≡
  with proposed-lemma-0 C′<:D fields-d≡
... | fenv-delta , fields-C′≡ =
  (fenv-delta ++ flds) ,
  (begin (fields C ≡⟨ {!!} ⟩ {!!}))


fields-ancestor :  ∀ {C}{D}
  → ∀ fenv-D i
  → fields D ≡ just fenv-D
  → ancestor (dcls CT) C i ≡ D
  → ∃[ fenv-C ]( fields C ≡ just fenv-C × ∃[ fenv-delta ] (fenv-D ++ fenv-delta ≡ fenv-C))
fields-ancestor {C}{D} fenv-D zero fields-D≡ anc-C-i≡D rewrite ancestor0 C anc-C-i≡D = fenv-D , fields-D≡ , [] , ++-identityʳ fenv-D
fields-ancestor {Object} {Object} [] (suc i) refl refl = [] , refl , [] , refl
fields-ancestor {Class cn} {.(ancestor (dcls CT) (Class cn) (suc i))} fenv-D (suc i) fields-D≡ refl
  = helper fenv-D fields-D≡ (declOf+ {name = ClassDecl.name} cn (dcls CT)) refl
  where
    helper : ∀ fenv-D → fields (ancestor (dcls CT) (Class cn) (suc i)) ≡ just fenv-D
      → (declc : ∃-syntax (λ cd → (dcls CT [ ClassDecl.name ]∋ cd) × ClassDecl.name cd ≡ cn) ⊎ (dcls CT [ ClassDecl.name ]∌ cn))
      → declc ≡ declOf+ {name = ClassDecl.name} cn (dcls CT)
      → ∃[ fenv-C ]( fields (Class cn) ≡ just fenv-C × ∃[ fenv-delta ] (fenv-D ++ fenv-delta ≡ fenv-C))
    helper fenv-D fields-D≡ (inj₁ ((class name extends exts field* flds method* mths) , cd∈ , refl)) eq rewrite eq = {!!}
    helper fenv-D fields-D≡ (inj₂ y) eq = {!!}


--   with declOf+ {name = ClassDecl.name} cn (dcls CT)
--... | decl-cn = {!!}

{-
  with declOf{name = ClassDecl.name} cn (dcls CT)
... | nothing = suc i , {!!}
... | just ((class .cn extends exts field* flds method* mths) , decl∈₂ , refl)
  with cc∋-functional decl∈₁ decl∈₂
... | refl , refl , refl = suc i , {!!}
-}

{-
-- rooted-mon : ∀ {C}{D}
--   → C <: D
--   → ∀ (rooted-D : Rooted (dcls CT) D)
--   → mRooted D ≡ just rooted-D
--   → ∃[ rooted-C ] (mRooted C ≡ just rooted-C)
-- rooted-mon S-Refl rooted-D mr-d≡ = rooted-D , mr-d≡
-- rooted-mon {Class cn} (S-Extends refl decl∈cd C<:D) rooted-D mr-d≡
--   with getRootedHelper (dcls CT) decl∈cd (sane CT)
-- ... | rooted-cn = {!!}
-}

height-mon : ∀ {C}{D}
  → C <: D
  → ∀ n
  → height D ≡ just n
  → ∃[ m ](height C ≡ just m × n ≤ m)
height-mon S-Refl n height-D = n , height-D , ≤-refl
height-mon {Class cn} (S-Extends refl decls∋ C<:D) n height-D
  with height-mon C<:D n height-D
... | m , height-C'≡ , n≤m = {!declOf+ {name = ClassDecl.name} cn (dcls CT)!}


{-
fields-mon : ∀ {C}{D}{T}
  → C <: D
  → ∀ fenv-D f
  → fields D ≡ just fenv-D → fenv-D [ Bind.name ]∋ (f ⦂ T)
  → ∃[ fenv-C ] (fields C ≡ just fenv-C × fenv-C [ Bind.name ]∋ (f ⦂ T))
fields-mon {C} {D} {T} C<:D fenv-D f fenv-D≡ f∈ = {!!}
-}
{-
fields-mon : ∀ {C}{D}{T}
  → C <: D
  → ∀ fenv-D f
  → fields D ≡ just fenv-D → fenv-D [ Bind.name ]∋ (f ⦂ T)
  → ∃[ fenv-C ] (fields C ≡ just fenv-C × fenv-C [ Bind.name ]∋ (f ⦂ T))
fields-mon S-Refl fenv-D f fenv-D≡ f∈ = fenv-D , fenv-D≡ , f∈
fields-mon {Class cn} {D} {T} (S-Extends {D = C′}{flds} refl decl-cn∈ C′<:D) fenv-D f fenv-D≡ f∈fenv-D
  with fields-mon {C′}{D}{T} C′<:D fenv-D f fenv-D≡ f∈fenv-D
... | fenv-C′ , fenv-C′≡ , f∈fenv-C′
  with flookup (Class cn)
... | just x = {!!}
... | nothing = {!!}
-}
{-
module an-alternative where
  fields-mon : ∀ {C}{D} → C <: D → ∀ fff-D → fields D ≡ just fff-D → ∃[ fff ] (fields C ≡ just (fff ++ fff-D))
  fields-mon {C} {.C} S-Refl fff-D fields-D≡ = [] , fields-D≡
  fields-mon {Class cn} {D} (S-Extends {D = C′} refl decls≡ C′<:D) fff-D fields-D≡
    with fields-mon C′<:D fff-D fields-D≡
  ... | fff , ih
    with flookup (Class cn) | flookup C′ | flookup D
  ... | just f0 | just fc | just fd = {!!}

fields-mon : ∀ {C}{D} → C <: D → ∀ fff-C → fields C ≡ just fff-C → ∃[ fff-D ] (fields D ≡ just fff-D)
fields-mon S-Refl fff-C field-C≡ = fff-C , field-C≡
fields-mon {Class cn} {Object} (S-Extends refl cd∈ C<:D) fff-cn field-C≡ = [] , refl
fields-mon {Class cn} {Class dn} (S-Extends {flds = flds}{mths = mths} refl cd∈ C<:D) fff-cn field-C≡
  with flookup (Class cn) | flookup (Class dn)
... | just x | just x₁ = {!!}
... | just x | nothing = {!!}
  -- where
  --   fields-mon-1 : fields (Class dn) ≡ just fff-D → fields (Class cn) ≡ just (flds ++ fff-D)
  --   fields-mon-1 
-}
