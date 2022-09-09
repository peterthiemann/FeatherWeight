module FJ.Syntax where

open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; proj₁; proj₂; _,_; ∃-syntax)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

retype : ∀ {ℓ}{A B : Set ℓ} → A → A ≡ B → B
retype a refl = a

Name = String

ClassName = Name
VarName = Name
MethName = Name
FieldName = Name

data Context  (A : Set) (get : A → Name) : Set where
  ∅  : Context A get
  _▷_ : Context A get → A → Context A get


toList : ∀ {A get} → Context A get → List A
toList ∅ = []
toList (Γ ▷ x) = x ∷ toList Γ

dom : ∀ {A get} → Context A get → List Name
dom {get = get} Γ = map get (toList Γ)

declOf : ∀ {A name} → (nm : Name) → Context A name → Maybe (Σ A (λ a → nm ≡ name a))
declOf nm ∅ = nothing
declOf {name = name} nm (Γ ▷ decl) with nm ≟ name decl
... | yes name≡ = just (decl , name≡)
... | no  name≢ = declOf nm Γ

_++_ : ∀ {A get} → Context A get → Context A get → Context A get
Γ ++ ∅ = Γ
Γ ++ (Δ ▷ x) = (Γ ++ Δ) ▷ x

data _∋_ {A name} : Context A name → A → Set where
  here  : ∀ {Γ : Context A name} {a : A} → (Γ ▷ a) ∋ a
  there : ∀ {Γ : Context A name} {a b : A} → Γ ∋ a → name a ≢ name b → (Γ ▷ b) ∋ a

decl→∋ : ∀ {A name} (Γ : Context A name) nm a p → declOf nm Γ ≡ just (a , p) → Γ ∋ a
decl→∋ {name = name} (Γ ▷ x) nm a p decl≡ with nm ≟ name x
decl→∋ {name = name} (Γ ▷ x) nm .x .nm≡ refl | yes nm≡ = here
decl→∋ {name = name} (Γ ▷ x) .(name a) a refl decl≡ | no nm≢ = there (decl→∋ Γ (name a) a refl decl≡) nm≢


record Bind (A B : Set) : Set where
  constructor _⦂_
  field
    name : A
    value : B

bound : ∀ {B} → Context (Bind Name B) Bind.name → List B
bound ∅ = []
bound (Γ ▷ (name ⦂ value)) = value ∷ bound Γ

----------------------------------------------------------------------
-- types

data Type : Set where
  Object : Type
  Class  : ClassName → Type

VarContext = Context (Bind VarName Type) Bind.name

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

Fields  = Context (Bind FieldName Type) Bind.name
Methods = Context MethDecl MethDecl.name

record ClassDecl : Set where
  constructor class_extends_field*_method*_
  field
    name : ClassName
    exts : Type
    flds : Fields
    mths : Methods
open ClassDecl

ClassContext = Context ClassDecl name

-- well-formed types occur in the class table

wf : ClassContext → Type → Set
wf cc Object = ⊤
wf cc (Class cn) = ∃[ cd ] declOf cn cc ≡ just cd

-- well-formed expressions refer to well-formed types

wf-e* : ClassContext → List Exp → Set
wf-e : ClassContext → Exp → Set
wf-e cc (Var x) = ⊤
wf-e cc (Field e f) = wf-e cc e
wf-e cc (Meth e m es) = wf-e cc e × wf-e* cc es
wf-e cc (New T es) = wf cc T × wf-e* cc es
wf-e cc (Cast T e) = wf cc T × wf-e cc e
wf-e cc (If e e₁ e₂) = wf-e cc e × wf-e cc e₁ × wf-e cc e₂

wf-e* cc [] = ⊤
wf-e* cc (e ∷ es) = wf-e cc e × wf-e* cc es

-- well-formed method declarations refer to well-formed types and expressions

wf-T* : ClassContext → VarContext → Set
wf-T* cc ∅ = ⊤
wf-T* cc (vc ▷ (_ ⦂ T)) = wf cc T × wf-T* cc vc

wf-m : ClassContext → MethDecl → Set
wf-m cc (method _ ⦂ args ⇒ ty return body) = wf-T* cc args × wf cc ty × wf-e cc body

wf-m* : ClassContext → Methods → Set
wf-m* cc ∅ = ⊤
wf-m* cc (mths₁ ▷ md) = wf-m cc md × wf-m* cc mths₁

-- well-formed class declarations ...

wf-c : ClassContext → ClassDecl → Set
wf-c cc (class _ extends exts₁ field* flds₁ method* mths₁) = wf cc exts₁ × wf-T* cc flds₁ × wf-m* cc mths₁

wf-c* : ClassContext → ClassContext → Set
wf-c* cc ∅ = ⊤
wf-c* cc (Γ ▷ cd) = wf-c cc cd × wf-c* cc Γ

-- helpers for further class wellformedness conditions

ancestor : ClassContext → Type → ℕ → Type
ancestor cc Object n = Object
ancestor cc T@(Class cn) zero = T
ancestor cc T@(Class cn) (suc n) with declOf cn cc
... | nothing = T
... | just (class name extends exts field* flds method* mths , refl) = ancestor cc exts n

Rooted : ClassContext → Type → Set
Rooted cc T = ∃[ n ] ancestor cc T n ≡ Object

check-uniq : ClassContext → FieldName → Type → Set
check-uniq dcls f Object = ⊤
check-uniq dcls f (Class cn) with declOf cn dcls
... | nothing = ⊤               -- unreachable
... | just (cd , _) = declOf f (flds cd) ≡ nothing

record ClassTable : Set where
  field
    dcls : ClassContext
         -- all class are well-formed
    defd : wf-c* dcls dcls
         -- all inheritance chains are rooted in Object (i.e., inheritance is acyclic)
    sane : All (λ cn → Rooted dcls (Class cn)) (dom dcls)
         -- field declarations are unique along inheritance chains
    uniq : All (λ{ cd → ∀ f → maybe (λ{ _ → ∀ n → check-uniq dcls f (ancestor dcls (Class (name cd)) (suc n)) }) ⊤ (declOf f (flds cd))})
               (toList dcls)
open ClassTable

wf₀ : ClassTable → Type → Set
wf₀ CT = wf (dcls CT)

wf* : ClassTable → VarContext → Set
wf* CT = wf-T* (dcls CT)

height′ : (T : Type) → {cc : ClassContext} → (ns : ClassContext) → (wt : wf ns T) → All (λ cn → Rooted cc (Class cn)) (dom ns) → Rooted cc T
height′ Object ns wt sct = 0 , refl
height′ (Class cn) ∅ () []
height′ (Class cn) (ns ▷ cd) wt (px ∷ sct) with cn ≟ name cd
... | no  cn≢x = height′ (Class cn) ns wt sct
height′ (Class cn) (ns ▷ cd) wt (rooted ∷ _) | yes refl = rooted

height : (CT : ClassTable) → (T : Type) → wf₀ CT T → ℕ
height CT T wt = proj₁ (height′ T (dcls CT) wt (sane CT))
