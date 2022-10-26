open import FJ.Syntax
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃-syntax; Σ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

module FJ.Lookup (CT : ClassTable) where

open ClassTable
open ClassDecl

_++ᴬ_ : ∀ {A : Set}{P : A → Set}{xx yy : List A} → All P xx → All P yy → All P (xx ++ yy) 
[] ++ᴬ ys = ys
(px ∷ xs) ++ᴬ ys = px ∷ xs ++ᴬ ys

getWellformedHelper : ∀ {cd} (cc : ClassContext) → cc [ name ]∋ cd → wf-c* (dcls CT) cc → wf-c (dcls CT) cd
getWellformedHelper [] () wfc*
getWellformedHelper (cd ∷ cc) (here x₁) (wfc-cd ∷ wfc*) = wfc-cd
getWellformedHelper (_ ∷ cc) (there cd∈cc x₁) (px ∷ wfc*) = getWellformedHelper cc cd∈cc wfc*

getWellformed : ∀ {cd} → dcls CT [ name ]∋ cd → wf-c (dcls CT) cd
getWellformed {cd} cd∈ = getWellformedHelper (dcls CT) cd∈ (defd CT)

getRootedHelper : ∀ {cd} (cc : ClassContext) → cc [ name ]∋ cd → All (λ cd → Rooted (dcls CT) (Class (name cd))) cc
  → Rooted (dcls CT) (Class (name cd))
getRootedHelper [] () san
getRootedHelper (_ ∷ _) (here cd∉) (px ∷ san) = px
getRootedHelper (_ ∷ cc) (there cd∈ x₁) (_ ∷ san) = getRootedHelper cc cd∈ san

getRooted : ∀ {cd} → dcls CT [ name ]∋ cd → Rooted (dcls CT) (Class (name cd))
getRooted {cd} cd∈ = getRootedHelper (dcls CT) cd∈ (sane CT)

mRooted : ∀ (T : Type) → Maybe (Rooted (dcls CT) T)
mRooted Object = just tt
mRooted (Class cn) with declOf{name = name} cn (dcls CT) in eq
... | nothing = nothing
... | just (cd@(class .cn extends exts₁ field* flds₁ method* mths₁) , cd∈ , refl)
  with getRootedHelper {cd} (dcls CT) cd∈ (sane CT)
... | rooted rewrite eq = just rooted

height : Type → Maybe ℕ
height Object = just 0
height T@(Class _) with mRooted T
... | nothing = nothing
... | just (n , rooted) = just n

getFields : ℕ → Type → Σ Fields (λ ff → wf-t*₀ CT ff)
getFields n Object = [] , []
getFields zero (Class cn) with declOf{name = name} cn (dcls CT)
... | nothing = [] , []
... | just (cd , cd∈ , cn≡) = flds cd , proj₁ (proj₂ (is-wf-cd{CT} cd∈))
getFields (suc n) (Class cn) with declOf{name = name} cn (dcls CT)
... | nothing = [] , []
... | just (cd , cd∈ , cn≡)
  with getFields n (exts cd)
... | ff , wft-ff = ff ++ flds cd , (wft-ff ++ᴬ proj₁ (proj₂ (is-wf-cd{CT} cd∈)) )

-- getFields : ℕ → Type → Fields
-- getFields n Object = []
-- getFields zero (Class cn) with declOf{name = name} cn (dcls CT)
-- ... | nothing = []
-- ... | just (cd , cd∈ , cn≡) = flds cd
-- getFields (suc n) (Class cn) with declOf{name = name} cn (dcls CT)
-- ... | nothing = []
-- ... | just (cd , cd∈ , cn≡) = getFields n (exts cd) ++ flds cd

flookup : Type → Maybe (Σ Fields (λ ff → wf-t*₀ CT ff))
flookup Object = just ([] , [])
flookup T@(Class cn) with height T
... | nothing = nothing
... | just n  = just (getFields (suc n) (Class cn))

fields  : Type → Maybe Fields
fields T = map proj₁ (flookup T)


mlookup-helper : (cn : ClassName) → MethName → (n : ℕ)
  → ancestor (dcls CT) (Class cn) n ≢ Object
  → ancestor (dcls CT) (Class cn) (suc n) ≡ Object
  → Maybe (Σ MethDecl (λ md → wf-m (dcls CT) md))
mlookup-helper cn mn n anc-n≢obj anc-n+1≡obj
  with declOf{name = name} cn (dcls CT) in decl-cn-eq
... | just ((class .cn extends exts₁ field* flds₁ method* mths₁) , cd∈ , refl)
  with declOf{name = MethDecl.name} mn mths₁
... | just (md , md∈ , refl) = just (md , (is-wf-md{CT} md∈ wf-mths₁))
    where
      wf-mths₁ : wf-m* (dcls CT) mths₁
      wf-mths₁ = proj₂ (proj₂ (is-wf-cd{CT} cd∈))
mlookup-helper cn mn zero anc-n≢obj anc-n+1≡obj | just ((class .cn extends exts₁ field* flds₁ method* mths₁) , cd∈ , refl) | nothing = nothing
mlookup-helper cn mn (suc n) anc-n≢obj anc-n+1≡obj | just ((class .cn extends exts₁ field* flds₁ method* mths₁) , cd∈ , refl) | nothing
  rewrite decl-cn-eq
  with ancestor1 {exts₁} n anc-n≢obj
... | cn-exts , refl = mlookup-helper cn-exts mn n anc-n≢obj anc-n+1≡obj

mlookup : MethName → Type → Maybe (Σ MethDecl (wf-m (dcls CT)))
mlookup mn Object = nothing
mlookup mn T@(Class cn) with mRooted T
... | nothing = nothing
... | just (n , anc-n≢obj , anc-n+1≡obj) = mlookup-helper cn mn n anc-n≢obj anc-n+1≡obj


mbody : MethName → Type → Maybe MethBody
mbody mn T = map (getMBody ∘ proj₁) (mlookup mn T)

mtype : MethName → Type → Maybe MethType
mtype mn T = map (getMType ∘ proj₁) (mlookup mn T)

