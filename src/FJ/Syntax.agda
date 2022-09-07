module FJ.Syntax where

open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.String using (String; _≟_)

open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

Name = String

ClassName = Name
VarName = Name
MethName = Name
FieldName = Name

data Context  (A : Set) (get : A → Name) : Set where
  ∅  : Context A get
  _▷_ : Context A get → A → Context A get

dom : ∀ {A get} → Context A get → List Name
dom ∅ = []
dom {get = get} (Γ ▷ x) = get x ∷ dom Γ 


declOf : ∀ {A name} → Name → Context A name → Maybe A
declOf nm ∅ = nothing
declOf {name = name} nm (Γ ▷ decl) with nm ≟ name decl
... | yes name≡ = just decl
... | no  name≢ = declOf nm Γ

_++_ : ∀ {A get} → Context A get → Context A get → Context A get
Γ ++ ∅ = Γ
Γ ++ (Δ ▷ x) = (Γ ++ Δ) ▷ x

toList : ∀ {A get} → Context A get → List A
toList ∅ = []
toList (Γ ▷ x) = x ∷ toList Γ


data _∋_ {A name} : Context A name → A → Set where
  here  : ∀ {Γ : Context A name} {a : A} → (Γ ▷ a) ∋ a
  there : ∀ {Γ : Context A name} {a b : A} → Γ ∋ a → name a ≢ name b → (Γ ▷ b) ∋ a

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

ClassContext = Context ClassDecl ClassDecl.name

ancestor : ClassContext → Type → ℕ → Type
ancestor cc Object n = Object
ancestor cc T@(Class cn) zero = T
ancestor cc T@(Class cn) (suc n) with declOf cn cc
... | nothing = T
... | just (class name extends exts field* flds method* mths) = ancestor cc exts n

record ClassTable : Set where
  field
    dcls : ClassContext
    sane : All (λ cn → ∃[ n ] ancestor dcls (Class cn) n ≡ Object) (dom dcls)
open ClassTable

height′ : Type → {cc : ClassContext} → (ns : List Name) → All (λ cn → ∃[ n ] ancestor cc (Class cn) n ≡ Object) ns → ℕ
height′ Object ns sct = 0
height′ (Class cn) [] [] = 0
height′ (Class cn) (x ∷ ns) (px ∷ sct) with cn ≟ x
... | no  cn≢x = height′ (Class cn) ns sct
height′ (Class cn) (x ∷ ns) ((n , _) ∷ _) | yes cn≡x = n

height : ClassTable → Type → ℕ
height CT T = height′ T (dom (dcls CT)) (sane CT)
