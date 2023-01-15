module FJ.Syntax where

open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_; map; lookup; length; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; proj₁; proj₂; _,_; ∃-syntax; ∃!)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Function using (_∘_)

open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; refl) renaming (cong to congᴴ)

Name = String

ClassName = Name
VarName = Name
MethName = Name
FieldName = Name

-- data Context  (A : Set) (get : A → Name) : Set where
--   ∅  : Context A get
--   _▷_ : Context A get → A → Context A get

-- c-len : ∀ {A}{g} → Context A g → ℕ
-- c-len ∅ = 0
-- c-len (Γ ▷ _) = suc (c-len Γ)

-- toList : ∀ {A get} → Context A get → List A
-- toList ∅ = []
-- toList (Γ ▷ x) = x ∷ toList Γ

-- c-len-len : ∀{A}{g} → (Γ : Context A g) → c-len Γ ≡ length (toList Γ)
-- c-len-len ∅ = refl
-- c-len-len (Γ ▷ _) = cong suc (c-len-len Γ)

-- c-len-dom : ∀{A}{g} → (Γ : Context A g) → c-len Γ ≡ length (dom Γ)
-- c-len-dom ∅ = refl
-- c-len-dom (Γ ▷ _) = cong suc (c-len-dom Γ)

-- declOf : ∀ {A name} → (nm : Name) → Context A name → Maybe (Σ A (λ a → nm ≡ name a))
-- declOf nm ∅ = nothing
-- declOf {name = name} nm (Γ ▷ decl) with nm ≟ name decl
-- ... | yes name≡ = just (decl , name≡)
-- ... | no  name≢ = declOf nm Γ

-- _++_ : ∀ {A get} → Context A get → Context A get → Context A get
-- Γ ++ ∅ = Γ
-- Γ ++ (Δ ▷ x) = (Γ ++ Δ) ▷ x

data _[_]∌_ {A : Set} : List A → (A → String) → String → Set where
  nowhere : ∀ {name}{cn} → [] [ name ]∌ cn
  nothere : ∀ {Γ : List A}{name}{cn}{a : A} → Γ [ name ]∌ cn → cn ≢ name a → (a ∷ Γ) [ name ]∌ cn

data _[_]∋_ {A : Set} : List A → (A → String) → A → Set where
  here  : ∀ {Γ : List A} {name} {a : A}   → ⊤ {- Γ [ name ]∌ name a -} → (a ∷ Γ) [ name ]∋ a
  there : ∀ {Γ : List A} {name} {a b : A} → Γ [ name ]∋ a → name a ≢ name b → (b ∷ Γ) [ name ]∋ a

member-exclusive : ∀ {A : Set}{name : A → String} {xs : List A} {x : A} → xs [ name ]∋ x → xs [ name ]∌ name x → ⊥
member-exclusive (here x) (nothere x∉ x≢x) = x≢x refl
member-exclusive (there x∈ x) (nothere x∉ x₁) = member-exclusive x∈ x∉

member-extension : ∀ {A : Set}{name : A → String}{ys : List A} {x} (xs : List A)
  → xs [ name ]∋ x → (xs ++ ys) [ name ]∋ x
member-extension .(_ ∷ _) (here x) =
  here tt
member-extension .(_ ∷ _) (there xs∋x name-x₁≢) =
  there (member-extension _ xs∋x) name-x₁≢

--   -- ≢-unique : ∀ {A : Set}{x y : A} → (p q : x ≢ y) → p ≡ q
--   -- ≢-unique p q = {!p refl!}

--   -- ∌-unique : ∀ {A} {name} {Γ : Context A name} {a} (p q : Γ ∌ a) → p ≡ q
--   -- ∌-unique nowhere nowhere = refl
--   -- ∌-unique (nothere p x) (nothere q x₁)
--   --   rewrite ∌-unique p q | ≢-unique x x₁ = refl

--   -- ∋-unique : ∀ {A} {name} {Γ : Context A name} {a}{b} (Γ∋a : Γ ∋ a) → (Γ∋b : Γ ∋ b) → name a ≡ name b → Γ∋a ≅ Γ∋b
--   -- ∋-unique (here x) (here x₁) refl rewrite ∌-unique x₁ x = refl
--   -- ∋-unique (here x) (there Γ∋b name≢) name-a≡b = ⊥-elim (name≢ (sym name-a≡b))
--   -- ∋-unique (there Γ∋a name≢) (here x₁) name-a≡b = ⊥-elim (name≢ name-a≡b)
--   -- ∋-unique (there Γ∋a x) (there Γ∋b x₁) name-a≡b
--   --   with ∋-unique Γ∋a Γ∋b name-a≡b
--   -- ... | ih = {!!}

--   ∃!-syntax : ∀ {a}{b}{A : Set a} → (A → Set b) → Set _
--   ∃!-syntax = ∃! _≡_
--   syntax ∃!-syntax (λ x → B) = ∃![ x ] B

--   ∌→¬lookup : ∀ {A name} {Γ : Context A name} a → Γ ∌ a → ∀ i → lookup (toList Γ) i ≢ a
--   ∌→¬lookup {A}{name} a (nothere Γ∌a name≢) zero = λ b≡a → name≢ (cong name (sym b≡a))
--   ∌→¬lookup a (nothere Γ∌a x) (suc i) = ∌→¬lookup a Γ∌a i

--   ∋→lookup! : ∀ {A name} {Γ : Context A name} a → Γ ∋ a → ∃![ i ] (lookup (toList Γ) i ≡ a)
--   ∋→lookup! a (here Γ∌a) = zero , refl , λ{ {zero} x → refl ; {suc y} lookup-y≡ → ⊥-elim (∌→¬lookup a Γ∌a y lookup-y≡)}
--   ∋→lookup! {A}{name} a (there Γ∋a n≢)
--     with ∋→lookup! a Γ∋a
--   ... | i , lookup≡ , lookup∀ = suc i , lookup≡ , (λ{ {zero} x → ⊥-elim (n≢ (cong name (sym x))) ; {suc y} x → cong suc (lookup∀ x)})

-- data _∋_ {A name} : Context A name → A → Set where
--   here  : ∀ {Γ : Context A name} {a : A} → (Γ ▷ a) ∋ a
--   there : ∀ {Γ : Context A name} {a b : A} → Γ ∋ a → name a ≢ name b → (Γ ▷ b) ∋ a

-- decl→∋ : ∀ {A name} (Γ : Context A name) nm a p → declOf nm Γ ≡ just (a , p) → Γ ∋ a
-- decl→∋ {name = name} (Γ ▷ x) nm a p decl≡ with nm ≟ name x
-- decl→∋ {name = name} (Γ ▷ x) nm .x .nm≡ refl | yes nm≡ = here
-- decl→∋ {name = name} (Γ ▷ x) .(name a) a refl decl≡ | no nm≢ = there (decl→∋ Γ (name a) a refl decl≡) nm≢

-- decl→lookup : ∀ {A name} (Γ : Context A name) nm a p → declOf nm Γ ≡ just (a , p) → ∃[ i ] lookup (toList Γ) i ≡ a
-- decl→lookup {name = name} (Γ ▷ x) nm a p decl≡ with nm ≟ name x
-- decl→lookup {name = name} (Γ ▷ x) .(name x) .x .refl refl | yes refl = zero , refl
-- ... | no nm≢
--   with decl→lookup Γ nm a p decl≡
-- ... | i , lookup≡ = suc i , lookup≡


record Bind (A B : Set) : Set where
  constructor _⦂_
  field
    name : A
    value : B

names : ∀ {B} → List (Bind Name B) → List Name
names = map Bind.name 

values : ∀ {B} → List (Bind Name B) → List B
values = map Bind.value

----------------------------------------------------------------------
-- types

data Type : Set where
  Object : Type
  Class  : ClassName → Type

VarContext = List (Bind VarName Type)

----------------------------------------------------------------------
-- expressions

data Exp : Set where
  Var    : VarName → Exp
  Field  : Exp → FieldName → Exp
  Meth   : Exp → MethName → List Exp → Exp
  New    : Type → List Exp → Exp
  Cast   : Type → Exp → Exp
  If     : Exp → Exp → Exp → Exp

MethArgs = VarContext
MethType = MethArgs × Type
MethBody = List VarName × Exp

record MethDecl : Set where
  constructor method_⦂_⇒_return_
  field
    name : MethName
    args : MethArgs
    ty   : Type
    body : Exp

Fields  = List (Bind FieldName Type)
Methods = List MethDecl

getMBody : MethDecl → MethBody
getMBody md = let open MethDecl in names (args md) , body md

getMType : MethDecl → MethType
getMType md = let open MethDecl in args md , ty md

record ClassDecl : Set where
  constructor class_extends_field*_method*_
  field
    name : ClassName
    exts : Type
    flds : Fields
    mths : Methods
open ClassDecl

ClassContext = List ClassDecl

-- decidable equality

_=T?_ : (S T : Type) → Dec (S ≡ T)
Object =T? Object = yes refl
Object =T? Class x = no λ()
Class x =T? Object = no λ()
Class x₁ =T? Class x₂
  with x₁ ≟ x₂
... | yes refl = yes refl
... | no  x₁≢x₂ = no (λ{ refl → x₁≢x₂ refl})

-- well-formed types

module wft-experimental where

  data WF-Type (cc : ClassContext) : {Type} → Set where
    Object : WF-Type cc {Object}
    Class  : ∀ {cd} → (cn : ClassName) → name cd ≡ cn → (cc [ name ]∋ cd) → WF-Type cc {Class cn}

  data WF-Exp (cc : ClassContext) : {Exp} → Set where
    Var    : (x : VarName) → WF-Exp cc {Var x}
    Field  : ∀ {e} → WF-Exp cc {e} → (f : FieldName) → WF-Exp cc {Field e f}

wf-t : ClassContext → Type → Set
wf-t cc Object = ⊤
wf-t cc (Class cn) = ∃[ cd ] (name cd ≡ cn × (cc [ name ]∋ cd))

-- well-formed expressions refer to well-formed types

wf-e* : ClassContext → List Exp → Set
wf-e  : ClassContext → Exp → Set
wf-e cc (Var x) = ⊤
wf-e cc (Field e f) = wf-e cc e
wf-e cc (Meth e m es) = wf-e cc e × wf-e* cc es
wf-e cc (New T es) = wf-t cc T × wf-e* cc es
wf-e cc (Cast T e) = wf-t cc T × wf-e cc e
wf-e cc (If e e₁ e₂) = wf-e cc e × wf-e cc e₁ × wf-e cc e₂

wf-e* cc [] = ⊤
wf-e* cc (e ∷ es) = wf-e cc e × wf-e* cc es

-- well-formed method declarations refer to well-formed types and expressions

wf-t* : ClassContext → VarContext → Set
wf-t* cc = All (λ{ (_ ⦂ T) → wf-t cc T})

wf-m : ClassContext → MethDecl → Set
wf-m cc (method _ ⦂ args ⇒ ty return body) = wf-t* cc args × wf-t cc ty × wf-e cc body

wf-m* : ClassContext → Methods → Set
wf-m* = All ∘ wf-m

-- well-formed class declarations ...

wf-c : ClassContext → ClassDecl → Set
wf-c cc (class _ extends exts₁ field* flds₁ method* mths₁) = wf-t cc exts₁ × wf-t* cc flds₁ × wf-m* cc mths₁

wf-c* : ClassContext → ClassContext → Set
wf-c* = All ∘ wf-c

-- extraction

wf-∈ : ∀ {cc : ClassContext} {x} {T} {Γ : VarContext}
  → wf-t* cc Γ
  → Γ [ Bind.name ]∋ (x ⦂ T)
  → wf-t cc T
wf-∈ [] ()
wf-∈ (px ∷ _) (here x) = px
wf-∈ (_ ∷ wft*) (there x∈Γ x₁) = wf-∈ wft* x∈Γ

-- helpers for further class wellformedness conditions

declNo : {A : Set}{name : A → Name} (cn : Name) (cc : List A) → Maybe (cc [ name ]∌ cn)
declNo cn [] = just nowhere
declNo {name = name} cn (cd ∷ cc) with name cd ≟ cn
... | yes cn≡ = nothing
... | no cn≢ with declNo cn cc
... | nothing = nothing
... | just cc∌ = just (nothere cc∌ (λ x → cn≢ (sym x)))

module experiment-obsolete where

  declOf : (cn : ClassName) (cc : ClassContext) → Maybe (∃[ cd ] cc [ name ]∋ cd × name cd ≡ cn)
  declOf cn [] = nothing
  declOf cn (cd ∷ cc) with name cd ≟ cn
  declOf cn (cd ∷ cc) | yes refl {- with declNo cn cc
  ... | nothing = nothing
  ... | just cc∌ -} = just (cd , here tt {- cc∌ -} , refl)
  declOf cn (cd ∷ cc) | no cn≢ with declOf cn cc
  ... | nothing = nothing
  ... | just (cd , cc∋cd , refl) = just (cd , there cc∋cd (λ x → cn≢ (sym x)) , refl)

module previous-version where

  declOf : {A : Set}{name : A → Name} (cn : Name) (cc : List A) → Maybe (∃[ cd ] cc [ name ]∋ cd × name cd ≡ cn)
  declOf cn [] = nothing
  declOf {name = name} cn (cd ∷ cc) with name cd ≟ cn
  ... | yes refl {- with declNo{name = name} cn cc
  ... | nothing = nothing
  ... | just cc∌ -} = just (cd , here tt {- cc∌ -} , refl)
  declOf {name = name} cn (cd ∷ cc) | no name≢ with declOf {name = name} cn cc
  ... | nothing = nothing
  ... | just (cd , cc∋cd , refl) = just (cd , ((there cc∋cd (name≢ ∘ sym)) , refl))

declOf+ : {A : Set}{name : A → Name} (cn : Name) (cc : List A) → (∃[ cd ] cc [ name ]∋ cd × name cd ≡ cn) ⊎ cc [ name ]∌ cn
declOf+ cn [] = inj₂ nowhere
declOf+ {name = name} cn (cd ∷ cc) with cn ≟ name cd
... | yes refl = inj₁ (cd , here tt , refl)
... | no name≢
  with declOf+ {name = name} cn cc
... | inj₁ (cd , cn∈ , refl) = inj₁ (cd , there cn∈ name≢ , refl)
... | inj₂ cn∉ = inj₂ (nothere cn∉ name≢)

declOf : {A : Set}{name : A → Name} (cn : Name) (cc : List A) → Maybe (∃[ cd ] cc [ name ]∋ cd × name cd ≡ cn)
declOf {A}{name} cn cc with
  declOf+ {A}{name} cn cc
... | inj₁ x = just x
... | inj₂ y = nothing

ancestor : ClassContext → Type → ℕ → Type
ancestor cc Object n = Object
ancestor cc T@(Class cn) zero = T
ancestor cc T@(Class cn) (suc n) with declOf+ {name = ClassDecl.name} cn cc
... | inj₂ _ = T
... | inj₁ (cd , cc∋ , refl) = ancestor cc (exts cd) n

ancestor0 : ∀ {T}{cc} → (T₁ : Type) → ancestor cc T₁ 0 ≡ T → T₁ ≡ T
ancestor0 Object refl = refl
ancestor0 (Class _) refl = refl

ancestor1 : ∀ {T}{cc} n → ancestor cc T n ≢ Object → ∃[ cn ] T ≡ Class cn
ancestor1 {Object} n anc-n≢object = ⊥-elim (anc-n≢object refl)
ancestor1 {Class cn} n anc-n≢object = cn , refl

Rooted : ClassContext → Type → Set
Rooted cc Object = ⊤
Rooted cc T@(Class x) = ∃[ n ] ancestor cc T n ≢ Object × ancestor cc T (suc n) ≡ Object

check-uniq : ClassContext → FieldName → Type → Set
check-uniq cc f Object = ⊤
check-uniq cc f (Class cn) with declOf {name = name} cn cc
... | nothing = ⊤               -- unreachable
... | just ((class _ extends exts field* flds method* mths) , _) = flds [ Bind.name ]∌ f

record ClassTable : Set where
  field
    dcls : ClassContext
         -- all class are well-formed
    defd : wf-c* dcls dcls
         -- all inheritance chains are rooted in Object (i.e., inheritance is acyclic)
    sane : All (λ cd → Rooted dcls (Class (name cd))) dcls
         -- field declarations are unique along inheritance chains
    uniq : All (λ cd → All (λ{ (f ⦂ _) → ∀ n → check-uniq dcls f (ancestor dcls (Class (name cd)) (suc n))}) (flds cd)) dcls
open ClassTable

wf-t₀ : ClassTable → Type → Set
wf-t₀ = wf-t ∘ dcls

wf-t*₀ : ClassTable → VarContext → Set
wf-t*₀ = wf-t* ∘ dcls

wf-e₀ : ClassTable → Exp → Set
wf-e₀ = wf-e ∘ dcls

wf-e*₀ : ClassTable → List Exp → Set
wf-e*₀ = wf-e* ∘ dcls

cc∋-functional : ∀ {cc}{cn}{e₁ e₂}{f₁ f₂}{m₁ m₂}
  → cc [ ClassDecl.name ]∋ (class cn extends e₁ field* f₁ method* m₁)
  → cc [ ClassDecl.name ]∋ (class cn extends e₂ field* f₂ method* m₂)
  → e₁ ≡ e₂ × f₁ ≡ f₂ × m₁ ≡ m₂
cc∋-functional (here x) (here x₁) = refl , refl , refl
cc∋-functional (here x) (there cc∋₂ cn≢cn) = ⊥-elim (cn≢cn refl)
cc∋-functional (there cc∋₁ cn≢cn) (here x₁) = ⊥-elim (cn≢cn refl)
cc∋-functional (there cc∋₁ x) (there cc∋₂ x₁) = cc∋-functional cc∋₁ cc∋₂

is-wf-cd : ∀ {CT} {cd} → dcls CT [ ClassDecl.name ]∋ cd → wf-c (dcls CT) cd
is-wf-cd {CT} cd∋ = is-wf-cd-helper {CT} (defd CT) cd∋
  where
    is-wf-cd-helper : ∀ {CT} {cd} {cc : ClassContext} → wf-c* (dcls CT) cc → cc [ ClassDecl.name ]∋ cd → wf-c (dcls CT) cd
    is-wf-cd-helper [] ()
    is-wf-cd-helper (px ∷ _) (here x) = px
    is-wf-cd-helper {CT} (_ ∷ cd∋) (there wf*-cc _) = is-wf-cd-helper{CT} cd∋ wf*-cc

is-wf-md : ∀ {CT} {mds}{md} → mds [ MethDecl.name ]∋ md → wf-m* (dcls CT) mds → wf-m (dcls CT) md
is-wf-md (here x) (px ∷ _) = px
is-wf-md {CT} (there md∋ x) (_ ∷ wf-mds) = is-wf-md {CT} md∋ wf-mds

