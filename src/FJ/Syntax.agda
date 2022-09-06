module FJ.Syntax where

open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat using (ℕ)
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

data Class : Set where
  Object : Class
  Extend : ClassName → Class → Class

data Type : Set where
  Ty : Class → Type

VarContext = Context (Bind VarName Type) Bind.name

bound : ∀ {B} → Context (Bind Name B) Bind.name → List B
bound ∅ = []
bound (Γ ▷ (name ⦂ value)) = value ∷ bound Γ


data Exp : Set where
  Var    : VarName → Exp
  Field  : Exp → FieldName → Exp
  Meth   : Exp → MethName → List Exp → Exp
  New    : Class → List Exp → Exp
  Cast   : Class → Exp → Exp
  If     : Exp → Exp → Exp → Exp

MethArgs = VarContext
MethType = MethArgs × Type
MethBody = List VarName × Exp

record MethDecl : Set where
  field
    name : MethName
    args : MethArgs
    ty   : Type
    body : Exp

Fields  = Context (Bind FieldName Type) Bind.name
Methods = Context MethDecl MethDecl.name

record ClassDecl : Set where
  constructor class_fls_mts_
  field
    name : ClassName
    flds : Fields
    mths : Methods

ClassTable = Context ClassDecl ClassDecl.name


declOf : ∀ {A name} → Name → Context A name → Maybe A
declOf nm ∅ = nothing
declOf {name = name} nm (Γ ▷ decl) with nm ≟ name decl
... | yes name≡ = just decl
... | no  name≢ = declOf nm Γ

