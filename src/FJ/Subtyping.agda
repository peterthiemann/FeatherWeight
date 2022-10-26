open import FJ.Syntax

module FJ.Subtyping (CT : ClassTable) where

open ClassTable

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; _≟_)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂; inspect; [_])
open import Relation.Nullary
  using (¬_; Dec; yes; no)

open import FJ.Lookup CT

-- subclass relation

data _<:_ : Type → Type → Set where
  S-Refl  : ∀ {C}
    → C <: C
  -- S-Trans : ∀ {C D E}
  --   → C <: D
  --   → D <: E
  --   → C <: E
  S-Extends : ∀ {C cn D flds mths E}
    → C ≡ Class cn
    -- → declOf cn (dcls CT) ≡ just (class cn extends D field* flds method* mths , {!!} , refl)
    → dcls CT [ ClassDecl.name ]∋ (class cn extends D field* flds method* mths)
    → D <: E
    → C <: E

S-Trans : ∀ {C D E} → C <: D → D <: E → C <: E
S-Trans S-Refl D<:E = D<:E
S-Trans (S-Extends C≡ dcls∋ C<:D) D<:E = S-Extends C≡ dcls∋ (S-Trans C<:D D<:E)

-- needs well-formedness of both, C and D
postulate
  <:-antisymm : ∀ {C D} → C <: D → D <: C → C ≡ D
-- <:-antisymm S-Refl S-Refl = refl
-- <:-antisymm S-Refl (S-Extends x x₁ D<:C) = {!!}
-- <:-antisymm (S-Extends x x₁ C<:D) S-Refl = {!!}
-- <:-antisymm (S-Extends x x₁ C<:D) (S-Extends x₂ x₃ D<:C) = {!!}


-- subclass lifted to lists of types

data _<:*_ : List Type → List Type → Set where
  S-Z : [] <:* []
  S-S : ∀ {C D Cs Ds} → C <: D → Cs <:* Ds → (C ∷ Cs) <:* (D ∷ Ds)

s-refl* : ∀ {Ts : List Type} → Ts <:* Ts
s-refl* {[]} = S-Z
s-refl* {T ∷ Ts} = S-S S-Refl s-refl*

s-trans* : ∀ {Ts Ts′ Ts″} → Ts <:* Ts′ → Ts′ <:* Ts″ → Ts <:* Ts″
s-trans* S-Z S-Z = S-Z
s-trans* (S-S T<:T′ Ts<:*Ts′) (S-S T′<:T″ Ts′<:*Ts″) = S-S (S-Trans T<:T′ T′<:T″) (s-trans* Ts<:*Ts′ Ts′<:*Ts″)

-- decidable subtyping (needed for preservation)

¬object<:class : ∀ {cn} → ¬ Object <: Class cn
¬object<:class (S-Extends () dcls∋ o<:cn)

class<:object : ∀ {cn} → Rooted (dcls CT) (Class cn) → Class cn <: Object
class<:object {cn} (n , anc-n≢object , anc-n+1≡object) = proof-of-cn<:object n anc-n≢object anc-n+1≡object
  where
    proof-of-cn<:object : ∀ {cn} → ∀ n
      → ancestor (dcls CT) (Class cn) n ≢ Object → ancestor (dcls CT) (Class cn) (suc n) ≡ Object
      → Class cn <: Object
    proof-of-cn<:object {cn} zero anc-n≢object anc-n+1≡object with declOf{name = ClassDecl.name} cn (dcls CT)
    ... | just ((class name extends exts field* flds method* mths) , cd∈ , refl)
      rewrite sym (ancestor0 exts anc-n+1≡object) = S-Extends refl cd∈ S-Refl
    proof-of-cn<:object {cn} (suc n) anc-n≢object anc-n+1≡object with declOf{name = ClassDecl.name} cn (dcls CT)
    ... | just ((class name extends exts field* flds method* mths) , cd∈ , refl)
      with ancestor1 {exts} n anc-n≢object
    ... | cn-ext , refl
      with proof-of-cn<:object n anc-n≢object anc-n+1≡object
    ... | cn-ext<:object = S-Extends refl cd∈ cn-ext<:object

-- class-exts-injective : {cd₁ cd₂ : ClassDecl} → cd₁ ≡ cd₂ → ClassDecl.exts cd₁ ≡ ClassDecl.exts cd₂
-- class-exts-injective refl = refl

class<:class : ∀ {cn cn₂} → Rooted (dcls CT) (Class cn) → Dec (Class cn <: Class cn₂)
class<:class {cn}{cn₂} (n , anc-n≢object , anc-n+1≡object) = proof-of-cn<:cn {cn} n anc-n≢object anc-n+1≡object
  where
    proof-of-cn<:cn : ∀ {cn} n
      → ancestor (dcls CT) (Class cn) n ≢ Object → ancestor (dcls CT) (Class cn) (suc n) ≡ Object
      → Dec (Class cn <: Class cn₂)
    proof-of-cn<:cn {cn} n anc-n≢object anc-n+1≡object
      with cn ≟ cn₂
    ... | yes refl = yes S-Refl
    proof-of-cn<:cn {cn} zero anc-n≢object anc-n+1≡object | no cn≢
      with declOf{name = ClassDecl.name} cn (dcls CT)
    ... | just ((class .cn extends exts field* flds method* mths) , cd∈ , refl)
      with ancestor0 exts anc-n+1≡object
    ... | refl = no ¬cn<:cn₂
      where
        ¬cn<:cn₂ : ¬ (Class cn <: Class cn₂)
        ¬cn<:cn₂ S-Refl = cn≢ refl
        ¬cn<:cn₂ (S-Extends refl cd∈₂ obj<:cn₂) with cc∋-functional cd∈ cd∈₂
        ... | refl , refl , refl = ¬object<:class obj<:cn₂
    proof-of-cn<:cn {cn} (suc n) anc-n≢object anc-n+1≡object | no cn≢
      with declOf{name = ClassDecl.name} cn (dcls CT)
    ... | just ((class .cn extends exts field* flds method* mths) , cd∈ , refl)
      with ancestor1 {exts} n anc-n≢object
    ... | cn₁ , refl
      with proof-of-cn<:cn {cn₁} n anc-n≢object anc-n+1≡object
    ... | yes cn₁<:cn₂ = yes (S-Extends refl cd∈ cn₁<:cn₂)
    ... | no ¬cn₁<:cn₂ = no ¬cn<:cn₂
      where
        ¬cn<:cn₂ : ¬ (Class cn <: Class cn₂)
        ¬cn<:cn₂ S-Refl = cn≢ refl
        ¬cn<:cn₂ (S-Extends refl cd∈₂ cn₁<:cn₂)
          with cc∋-functional cd∈ cd∈₂
        ... | refl , refl , refl = ¬cn₁<:cn₂ cn₁<:cn₂

_[_]<:?_ : (S : Type) (ws : wf-t₀ CT S) (T : Type) → Dec (S <: T)
Object [ _ ]<:? Object = yes S-Refl
Object [ _ ]<:? Class x = no ¬object<:class
Class cn [ cd , refl , cd∈ ]<:? Object = yes (class<:object (getRooted cd∈))
Class cn [ cd , refl , cd∈ ]<:? Class cn₂ = class<:class (getRooted cd∈)

lemma-cd : ∀ {C}{D} → ¬ (D <: C) → C ≢ D
lemma-cd {Object} {Object} ¬C<:D = ⊥-elim (¬C<:D S-Refl)
lemma-cd {Object} {Class x} ¬C<:D = λ()
lemma-cd {Class x} {Object} ¬C<:D = λ()
lemma-cd {Class cn} {Class cn₁} ¬C<:D with cn ≟ cn₁
... | yes refl = ⊥-elim (¬C<:D S-Refl)
... | no  cn≢cn₁ = λ{ refl → ⊥-elim (cn≢cn₁ refl)}


lemma-cdd1 : ∀ {C D D′} → ¬ (C <: D) → (D′ <: D) → ¬ (C <: D′)
lemma-cdd1 ¬C<:D D′<:D C<:D′ = ¬C<:D (S-Trans C<:D′ D′<:D)

wf-<: : ∀ {S} {T} → S <: T → wf-t₀ CT T → wf-t₀ CT S
wf-<: S-Refl wft-T = wft-T
wf-<: (S-Extends refl cn∈cd S<:T) wft-T = _ , (refl , cn∈cd)


lemma-cdd2 : ∀ {C D D′} → wf-t₀ CT D → ¬ (D <: C) → (D′ <: D) → Dec (D′ <: C)
lemma-cdd2 wft-D ¬D<:C S-Refl = no ¬D<:C
lemma-cdd2 {Object} {Object} wft-D ¬D<:C (S-Extends refl x₁ D′<:D) = ⊥-elim (¬D<:C S-Refl)
lemma-cdd2 {Object} {Class dn} (cd-d , refl , cd-d∈) ¬D<:C (S-Extends refl x₁ D′<:D) = ⊥-elim (¬D<:C (class<:object (getRooted cd-d∈)))
lemma-cdd2 {Class cn} wft-D ¬D<:C (S-Extends {cn = dn′} refl dn′∈ D′<:D) = class<:class (getRooted dn′∈)

lemma-cdd3 : ∀ {C D D′} → C <: D → C <: D′ → D <: D′ ⊎ D′ <: D
lemma-cdd3 {Object} {.Object} {.Object} S-Refl S-Refl = inj₁ S-Refl
lemma-cdd3 {Class cn} {.(Class cn)} {D′} S-Refl C<:D′ = inj₁ C<:D′
lemma-cdd3 {Class cn} {D} {.(Class cn)} C<:D@(S-Extends x x₁ C<:D′) S-Refl = inj₂ C<:D
lemma-cdd3 {Class cn} {D} {D′} (S-Extends refl cn∈₁ C<:D) (S-Extends refl cn∈₂ C<:D′)
  with cc∋-functional cn∈₁ cn∈₂
... | refl , refl , refl = lemma-cdd3 C<:D C<:D′

¬C<:D⇒C≢D : ∀ {C}{D} → ¬ C <: D → C ≢ D
¬C<:D⇒C≢D ¬C<:D refl = ¬C<:D S-Refl

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
