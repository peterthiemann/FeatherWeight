open import FJ.Syntax
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.List using (List; map; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product
open import Data.String using (String; _≟_)
open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

module FJ.Lookup (CT : ClassTable) where

open ClassTable

fields′ : ℕ → Type → Fields
fields′ n Object = ∅
fields′ zero (Class cn) = ∅
fields′ (suc n) (Class cn) with declOf cn (dcls CT)
... | nothing = ∅
... | just (class name extends exts field* flds method* mths , refl) = fields′ n exts ++ flds

fields : Type → Fields
fields T = let n = height CT T in fields′ n T

mtype′ : ℕ → MethName → Type → Maybe MethType
mtype′ zero m T = nothing
mtype′ (suc n) m Object = nothing
mtype′ (suc n) m (Class cn) with declOf cn (dcls CT)
... | nothing = nothing
... | just (class name extends exts field* flds method* mths , refl) with declOf m mths
... | nothing = mtype′ n m exts
... | just (method _ ⦂ args ⇒ ty return body , refl) = just (args , ty)

mtype : MethName → Type → Maybe MethType
mtype m T = let n = height CT T in mtype′ n m T


mbody′ : ℕ → MethName → Type → Maybe MethBody
mbody′ zero m T = nothing
mbody′ (suc n) m Object = nothing
mbody′ (suc n) m (Class cn) with declOf cn (dcls CT)
... | nothing = nothing
... | just (class name extends exts field* flds method* mths , refl) with declOf m mths
... | nothing = mbody′ n m exts
... | just  (method _ ⦂ args ⇒ ty return body , refl) = just (dom args , body)

mbody : MethName → Type → Maybe MethBody
mbody m T = let n = height CT T in mbody′ n m T
