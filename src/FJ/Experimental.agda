open import FJ.Syntax

module FJ.Experimental (CT : ClassTable) where

open ClassTable

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just; Is-just; Is-nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.String using (String; _≟_)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂; inspect; [_])
open import Relation.Nullary
  using (¬_; Dec; yes; no)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)

open import FJ.Lookup CT
open import FJ.Subtyping CT

fields' : ∀ {C} → C <: Object → Fields
fields' S-Refl = []
fields' (S-Extends {C}{cn}{C′}{flds}{mths}{Object} C≡Class-cn decls∋cn C′<:Obj) =
  fields' C′<:Obj ++ flds

get-separate-fields : ∀ {C} → C <: Object → Fields × Fields
get-separate-fields {.Object} S-Refl = [] , []
get-separate-fields {C} (S-Extends {C}{cn}{C′}{flds}{mths}{Object} C≡Class-cn decls∋cn C′<:Obj) = proj₁ (get-separate-fields C′<:Obj) ++ proj₂ (get-separate-fields C′<:Obj) , flds

fields'≡separate-fields : ∀ {C} → (s : C <: Object) → fields' s ≡ (proj₁ (get-separate-fields s) ++ proj₂ (get-separate-fields s))
fields'≡separate-fields {.Object} S-Refl = refl
fields'≡separate-fields {C} (S-Extends {C}{cn}{C′}{flds}{mths}{Object} C≡Class-cn decls∋cn C′<:Obj)
  with get-separate-fields C′<:Obj | fields'≡separate-fields{C′} C′<:Obj
... | fst , snd | b rewrite b | sym (++-identityʳ (fst ++ snd)) = refl

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

class-eq-names-eq : ∀ {cn cn'} → Class cn ≡ Class cn' → cn ≡ cn'
class-eq-names-eq {cn} {.cn} refl = refl

-- Uniqueness of []∈
in-unique : ∀ {A : Set} {B : A → String} {Γ : List A} {a : A} → (ins ins' : Γ [ B ]∋ a) → ins ≡ ins'
in-unique {A} {B} {.(a ∷ _)} {a} (here x) (here x₁) = refl
in-unique {A} {B} {.(a ∷ _)} {a} (here x) (there ins' x₁) = ⊥-elim (x₁ refl)
in-unique {A} {B} {.(a ∷ _)} {a} (there ins x) (here x₁) = ⊥-elim (x refl)
in-unique {A} {B} {.(_ ∷ _)} {a} (there ins x) (there ins' x₁) = cong₂ there (in-unique ins ins') {!!}

-- Uniqueness of class declarations
-- => cant prove uniqueness of a ≢ b => need this as an assumption...
dcls-eq : ∀ {cd} → (a b : dcls CT [ ClassDecl.name ]∋ cd) → a ≡ b
dcls-eq {cd} (here x) (here x₁) = refl
dcls-eq {cd} (here x) (there b x₁) = ⊥-elim (x₁ refl)
dcls-eq {cd} (there a x) (here x₁) = ⊥-elim (x refl)
dcls-eq {cd} (there a x) (there b x₁) = cong₂ there {!dcls-eq a b!} {!!}

-- Uniqueness of s s' : (C <: Object) by uniqueness of ancestor 1
<:-object-unique : ∀ {C} → (s s' : C <: Object) → s ≡ s'
<:-object-unique S-Refl S-Refl = refl
<:-object-unique (S-Extends {.(Class cn)}{cn}{D}{flds}{mths}{Object} refl decls∋cn D<:Object) (S-Extends {.(Class cn)}{.cn}{D'}{flds'}{mths'}{Object} refl decls∋cn' D′<:Object)
  with (cc∋-functional decls∋cn decls∋cn')
... | eq , eq' , eq'' rewrite eq | eq' | eq'' | (<:-object-unique D<:Object D′<:Object) | (dcls-eq decls∋cn decls∋cn') = refl

-- Relating ancestors and extensions
ancestor-1-extends : ∀ {C D cn} → C ≡ Class cn → (s : C <: Object) → (ancestor (dcls CT) C (suc 0) ≡ D) → ∃[ flds ](∃[ mths ]( dcls CT [ ClassDecl.name ]∋ (class cn extends D field* flds method* mths) ))
ancestor-1-extends {C} {D} {cn} refl (S-Extends {C}{.cn}{C′}{flds'}{mths'}{Object} refl decls∋cn C′<:Object) anc≡
  with declOf+ {name = ClassDecl.name} cn (dcls CT)
... | inj₂ decl∉ = ⊥-elim (member-exclusive decls∋cn decl∉)
... | inj₁ ((class .cn extends exts field* flds method* mths) , decl∈₂ , refl) rewrite sym (ancestor0{D}{cc = dcls CT} exts anc≡) = flds , (mths , decl∈₂)

extends-ancestor-1 : ∀ {C D flds mths cn} → C ≡ Class cn → (s : C <: Object) → dcls CT [ ClassDecl.name ]∋ (class cn extends D field* flds method* mths) → (ancestor (dcls CT) C (suc 0) ≡ D)
extends-ancestor-1 {.(Class cn)} {D} {flds} {mths} {cn} refl (S-Extends {C}{.cn}{C′}{flds'}{mths'}{Object} refl decls∋cn C′<:Object) dcl = {!!}

separate-fields-parent : ∀ {C D} → (s : C <: Object) → (s' : D <: Object) → (ancestor (dcls CT) C (suc 0) ≡ D) → (proj₁ (get-separate-fields s) ≡ fields' s')
separate-fields-parent {.Object} {.(ancestor (dcls CT) Object 1)} S-Refl S-Refl refl = refl
separate-fields-parent {C} {D} leq@(S-Extends {C}{cn}{C′}{flds}{mths}{Object} C≡Class-cn decls∋cn C′<:Object) s' anc≡
  with ancestor-1-extends C≡Class-cn leq anc≡
... | fst , snd , dcl
  with cc∋-functional dcl decls∋cn
... | eq , eq' , eq'' rewrite eq | eq' | eq'' rewrite (<:-object-unique C′<:Object s') = sym (fields'≡separate-fields s')

fields'Object≡[] : (s : Object <: Object) → fields' s ≡ []
fields'Object≡[] S-Refl = refl

proposed-lemma-0' : ∀ {C}{D}{fenv-d}
  → C <: D
  → (s : C <: Object)
  → (s' : D <: Object)
  → fields' s' ≡ fenv-d
  → ∃[ fenv-delta ] (fields' s ≡ (fenv-d ++ fenv-delta))
proposed-lemma-0' {C} {fenv-d = fenv-d} S-Refl cobj dobj fields-d≡ rewrite (<:-object-unique cobj dobj) = [] , (trans fields-d≡ (sym (++-identityʳ fenv-d)))
proposed-lemma-0' {C} {fenv-d = fenv-d} (S-Extends {C}{cn}{C′}{flds}{mths}{D} C≡Class-cn decls∋cn C′<:D) cobj dobj fields-d≡
  with proposed-lemma-0' C′<:D (S-Trans C′<:D dobj) dobj fields-d≡ | extends-ancestor-1 C≡Class-cn cobj decls∋cn
... | fenv-delta , fields-C′≡ | anc≡ rewrite C≡Class-cn
  with separate-fields-parent cobj (S-Trans C′<:D dobj) anc≡
... | fields-s'≡ rewrite (fields'≡separate-fields cobj) | (trans fields-s'≡ fields-C′≡) = fenv-delta ++ proj₂ (get-separate-fields cobj) , ++-assoc fenv-d fenv-delta (proj₂ (get-separate-fields cobj))

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
... | m , height-C'≡ , n≤m
  = {!declOf+ {name = ClassDecl.name} cn (dcls CT)!}


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




