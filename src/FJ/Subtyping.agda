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
  S-Extends : ∀ {C}{cn}{D}{flds}{mths}{E}
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

class<:object : ∀{cn} → Rooted (dcls CT) (Class cn) → Class cn <: Object
class<:object (rooted-cls {class _ extends exts field* _ method* _} ∋cd namecd≡cn proof)
  with exts
... | Object = S-Extends (sym (cong Class namecd≡cn)) ∋cd S-Refl
... | Class cn = S-Extends (sym (cong Class namecd≡cn)) ∋cd (class<:object proof)

-- class-exts-injective : {cd₁ cd₂ : ClassDecl} → cd₁ ≡ cd₂ → ClassDecl.exts cd₁ ≡ ClassDecl.exts cd₂
-- class-exts-injective refl = refl

¬C<:D→C≢D : ∀ {C}{D} → ¬ (D <: C) → C ≢ D
¬C<:D→C≢D {Object} {Object} ¬C<:D = ⊥-elim (¬C<:D S-Refl)
¬C<:D→C≢D {Object} {Class x} ¬C<:D = λ()
¬C<:D→C≢D {Class x} {Object} ¬C<:D = λ()
¬C<:D→C≢D {Class cn} {Class cn₁} ¬C<:D with cn ≟ cn₁
... | yes refl = ⊥-elim (¬C<:D S-Refl)
... | no  cn≢cn₁ = λ{ refl → ⊥-elim (cn≢cn₁ refl)}

eq-or-sub : ∀{C₁ C₂ C₁ₛ cn₁ fs ms} → Class cn₁ ≡ C₁ → C₁ <: C₂ → ( dcls CT [ ClassDecl.name ]∋ (class cn₁ extends C₁ₛ field* fs method* ms)) → C₁ ≡ C₂ ⊎ C₁ₛ <: C₂
eq-or-sub refl S-Refl ∋cd = inj₁ refl
eq-or-sub refl (S-Extends refl ∋cd' D<:C₂) ∋cd
  with c-uniq CT ∋cd ∋cd'
... | refl , refl = inj₂ D<:C₂

eq-or-sub→⊥ : ∀{C₁ C₁ₛ C₂} → ¬ C₁ ≡ C₂ → ¬ C₁ₛ <: C₂ → C₁ ≡ C₂ ⊎ C₁ₛ <: C₂ → ⊥
eq-or-sub→⊥ ¬eq ¬sub (inj₁ eq) = ¬eq eq
eq-or-sub→⊥ ¬eq ¬sub (inj₂ sub) = ¬sub sub

¬cn→¬C : ∀{cn₁ cn₂} → ¬ cn₁ ≡ cn₂ → ¬ (Class cn₁) ≡ (Class cn₂)
¬cn→¬C ¬eq refl = ¬eq refl

-- TODO : get rid of this confusion two names
_<:[_]?_ : (t₁ : Type) → Rooted (dcls CT) t₁ → (t₂ : Type) → Dec (t₁ <: t₂)
Object <:[ proof ]? Object = yes S-Refl
Object <:[ proof ]? Class x = no ¬object<:class
Class cn₁ <:[ proof ]? Object = yes (class<:object proof)
Class cn₁ <:[ rooted-cls {cd@(class _ extends cn₁ₛ field* _ method* _)} ∋cd refl proof ]? Class cn₂
  with cn₁ ≟ cn₂
... | yes refl = yes S-Refl
... | no ¬cn₁≡cn₂
  with cn₁ₛ <:[ proof ]? Class cn₂
... | yes cn₁ₛ<:cn₂ = yes (S-Extends refl ∋cd cn₁ₛ<:cn₂)
... | no ¬cn₁ₛ<:cn₂ = no λ cn₁<:cn₂ → eq-or-sub→⊥ (¬cn→¬C ¬cn₁≡cn₂) ¬cn₁ₛ<:cn₂ (eq-or-sub refl cn₁<:cn₂ ∋cd)

_[_]<:?_ : (S : Type) (ws : wf-t₀ CT S) (T : Type) → Dec (S <: T)
Object [ _ ]<:? Object = yes S-Refl
Object [ _ ]<:? Class x = no ¬object<:class
Class cn [ cd , refl , ∋cd ]<:? Object = yes (class<:object (sane CT ∋cd))
Class cn [ cd , refl , ∋cd ]<:? Class cn₂ = (Class (ClassDecl.name cd)) <:[ sane CT ∋cd ]? Class cn₂

lemma-somewhere : ∀(C D : Type) → wf-t₀ CT C → wf-t₀ CT D → C <: D × C ≢ D ⊎ D <: C ⊎ ¬ (C <: D) × ¬ (D <: C)
lemma-somewhere c d ws₁ ws₂ with c [ ws₁ ]<:? d | d [ ws₂ ]<:? c
... | yes c<:d | yes d<:c = inj₂ (inj₁ d<:c)
... | yes c<:d | no  d≮:c = inj₁ (c<:d , λ{ refl → d≮:c S-Refl})
... | no  c≮:d | yes d<:c = inj₂ (inj₁ d<:c)
... | no  c≮:d | no  d≮:c = inj₂ (inj₂ (c≮:d , d≮:c))

lemma-cd1 : ∀{C D} → (C <: D) ⊎ (D <: C) → ¬(C <: D) → ¬(D <: C) → ⊥
lemma-cd1 (inj₁ CD) ¬CD ¬DC = ¬CD CD
lemma-cd1 (inj₂ DC) ¬CD ¬DC = ¬DC DC

lemma-cdd1 : ∀ {C D D′} → ¬ (C <: D) → (D′ <: D) → ¬ (C <: D′)
lemma-cdd1 ¬C<:D D′<:D C<:D′ = ¬C<:D (S-Trans C<:D′ D′<:D)

wf-<: : ∀ {S} {T} → S <: T → wf-t₀ CT T → wf-t₀ CT S
wf-<: S-Refl wft-T = wft-T
wf-<: (S-Extends refl cn∈cd S<:T) wft-T = _ , (refl , cn∈cd)

lemma-cdd2 : ∀ {C D D′} → wf-t₀ CT D → ¬ (D <: C) → (D′ <: D) → Dec (D′ <: C)
lemma-cdd2 wft-D ¬D<:C S-Refl = no ¬D<:C
lemma-cdd2 {Object} {Object} wft-D ¬D<:C (S-Extends refl x₁ D′<:D) = ⊥-elim (¬D<:C S-Refl)
lemma-cdd2 {Object} {Class dn} (cd-d , refl , cd-d∈) ¬D<:C (S-Extends refl x₁ D′<:D) = ⊥-elim (¬D<:C (class<:object (sane CT cd-d∈)))
lemma-cdd2 {Class cn} wft-D ¬D<:C (S-Extends {cn = dn′} refl dn′∈ D′<:D) = (Class dn′) <:[ sane CT dn′∈ ]? (Class cn)

lemma-cdd3 : ∀ {C D D′} → C <: D → C <: D′ → D <: D′ ⊎ D′ <: D
lemma-cdd3 {Object} {.Object} {.Object} S-Refl S-Refl = inj₁ S-Refl
lemma-cdd3 {Class cn} {.(Class cn)} {D′} S-Refl C<:D′ = inj₁ C<:D′
lemma-cdd3 {Class cn} {D} {.(Class cn)} C<:D@(S-Extends x x₁ C<:D′) S-Refl = inj₂ C<:D
lemma-cdd3 {Class cn} {D} {D′} (S-Extends refl cn∈₁ C<:D) (S-Extends refl cn∈₂ C<:D′)
  with cc∋-functional cn∈₁ cn∈₂
... | refl , refl , refl = lemma-cdd3 C<:D C<:D′

¬C<:D⇒C≢D : ∀ {C}{D} → ¬ C <: D → C ≢ D
¬C<:D⇒C≢D ¬C<:D refl = ¬C<:D S-Refl

nothing≡just→⊥ : ∀{x : Fields} → nothing ≡ just x → ⊥
nothing≡just→⊥ ()
