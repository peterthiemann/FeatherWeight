open import FJ.Syntax

module FJ.Subtyping (CT : ClassTable) where

open ClassTable

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; _≟_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂; inspect; [_])
open import Relation.Nullary
  using (¬_; Dec; yes; no)

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
    → declOf cn (dcls CT) ≡ just (class cn extends D field* flds method* mths , refl)
    -- → dcls CT ∋ (class cn extends D field* flds method* mths)
    → D <: E
    → C <: E

S-Trans : ∀ {C D E} → C <: D → D <: E → C <: E
S-Trans S-Refl D<:E = D<:E
S-Trans (S-Extends C≡ dcls∋ C<:D) D<:E = S-Extends C≡ dcls∋ (S-Trans C<:D D<:E)

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
class<:object {cn} (n , anc-n≡object) = proof-of-cn<:object (Class cn) n anc-n≡object
  where
    proof-of-cn<:object : (T : Type) → ∀ n → ancestor (dcls CT) T n ≡ Object → T <: Object
    proof-of-cn<:object Object zero anc-n≡object = S-Refl
    proof-of-cn<:object Object (suc n) anc-n≡object = S-Refl
    proof-of-cn<:object (Class cn) (suc n) anc-n≡object with declOf cn (dcls CT) | inspect (declOf cn) (dcls CT)
    ... | just ((class .cn extends exts field* flds method* mths) , refl) | [ eq ] = S-Extends refl eq (proof-of-cn<:object exts n anc-n≡object)

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

pair-injective₁ : ∀ {A : Set} {B : A → Set} {a1 a2 : Σ A B} → a1 ≡ a2 → proj₁ a1 ≡ proj₁ a2
pair-injective₁ refl = refl

class-exts-injective : {cd₁ cd₂ : ClassDecl} → cd₁ ≡ cd₂ → ClassDecl.exts cd₁ ≡ ClassDecl.exts cd₂
class-exts-injective refl = refl

class<:class : ∀ {T}{cn₂} → (ws : wf₀ CT T) → Rooted (dcls CT) T → Dec (T <: Class cn₂)
class<:class{T}{cn₂} ws (n , anc-n≡object) = proof-of-cn<:cn T n anc-n≡object
  where
    proof-of-cn<:cn : (T : Type) → ∀ n → ancestor (dcls CT) T n ≡ Object → Dec (T <: Class cn₂)
    proof-of-cn<:cn Object n anc-n≡object = no ¬object<:class
    proof-of-cn<:cn (Class cn₁) (suc n) anc-n≡object with cn₁ ≟ cn₂
    ... | yes refl = yes S-Refl
    ... | no  cn₁≢cn₂ with declOf cn₁ (dcls CT) | inspect (declOf cn₁) (dcls CT)
    ... | just ((class .cn₁ extends exts field* flds method* mths) , refl) | [ eq ]
      with proof-of-cn<:cn exts n anc-n≡object
    ... | yes exts<:cn₂ = yes (S-Extends refl eq exts<:cn₂)
    ... | no ¬exts<:cn₂ = no (λ{ S-Refl → ⊥-elim (cn₁≢cn₂ refl)
                               ; (S-Extends refl declOf≡ D<:cn₂) →
                                            ¬exts<:cn₂ (retype D<:cn₂ (cong (_<: Class cn₂) (class-exts-injective (pair-injective₁ (just-injective (trans (sym declOf≡) eq))))))})

_[_]<:?_ : (S : Type) (ws : wf₀ CT S) (T : Type) → Dec (S <: T)
Object [ _ ]<:? Object = yes S-Refl
Object [ _ ]<:? Class cn = no ¬object<:class
Class cn [ ws ]<:? Object = yes (class<:object (height′ (Class cn) (dcls CT) ws (sane CT)))
Class cn [ ws ]<:? Class cn₁ = class<:class ws (height′ (Class cn) (dcls CT) ws (sane CT))

lemma-cd : ∀ {C}{D} → ¬ (D <: C) → C ≢ D
lemma-cd {Object} {Object} ¬C<:D = ⊥-elim (¬C<:D S-Refl)
lemma-cd {Object} {Class x} ¬C<:D = λ()
lemma-cd {Class x} {Object} ¬C<:D = λ()
lemma-cd {Class cn} {Class cn₁} ¬C<:D with cn ≟ cn₁
... | yes refl = ⊥-elim (¬C<:D S-Refl)
... | no  cn≢cn₁ = λ{ refl → ⊥-elim (cn≢cn₁ refl)}



lemma-cdd1 : ∀ {C D D′} → ¬ (C <: D) → (D′ <: D) → ¬ (C <: D′)
lemma-cdd1 ¬C<:D D′<:D C<:D′ = ¬C<:D (S-Trans C<:D′ D′<:D)

lemma-cdd2 : ∀ {C D D′} → wf₀ CT D → ¬ (D <: C) → (D′ <: D) → Dec (D′ <: C)
lemma-cdd2 wfd ¬D<:C S-Refl = no (λ  D′<:C → ¬D<:C D′<:C)
lemma-cdd2 {Object} {Object} wfd ¬D<:C (S-Extends {cn = cn} {D = D₁} D′≡Class-cn x₁ D′<:D) = ⊥-elim (¬D<:C S-Refl)
lemma-cdd2 {Object} {Class x} wfd ¬D<:C (S-Extends {cn = cn} {D = D₁} D′≡Class-cn x₁ D′<:D) = ⊥-elim (¬D<:C (class<:object (height′ (Class x) (dcls CT) wfd (sane CT))))
lemma-cdd2 {Class cn₂} wfd ¬D<:C (S-Extends {cn = cn₁} {D = D₁} refl x₁ D₁<:D) with cn₁ ≟ cn₂
... | yes refl = yes S-Refl
... | no  cn₁≢cn₂ with lemma-cdd2 wfd ¬D<:C D₁<:D
... | yes D₁<:Class-cn₂ = yes (S-Extends refl x₁ D₁<:Class-cn₂)
... | no ¬D₁<:Class-cn₂ = no (λ{ S-Refl → ⊥-elim (cn₁≢cn₂ refl)
                               ; (S-Extends refl declOf≡ D₂<:Class-cn₂) →
                                            ¬D₁<:Class-cn₂ (retype D₂<:Class-cn₂ (cong (_<: Class cn₂) (class-exts-injective (pair-injective₁ (just-injective (trans (sym declOf≡) x₁))))))})
