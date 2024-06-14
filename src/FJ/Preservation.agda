open import FJ.Syntax

module FJ.Preservation (CT : ClassTable) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.List using (List; []; _∷_; _++_; lookup; length; map)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_,_; proj₁; proj₂; _×_; Σ; Σ-syntax; ∃; ∃-syntax)
open import Data.String using (String; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

open import Relation.Binary.HeterogeneousEquality
  using (_≅_; ≅-to-type-≡; ≅-to-subst-≡ )
open import Function using (_∘_)

open import FJ.Lookup CT
open import FJ.Subtyping CT
open import FJ.Reduction CT
open import FJ.Typing CT
open import FJ.TypingProperties CT

-- general utilities

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

pair-injective₁ : ∀ {A : Set} {B : A → Set} {a1 a2 : Σ A B} → a1 ≡ a2 → proj₁ a1 ≡ proj₁ a2
pair-injective₁ refl = refl

pair-injective₂ : ∀ {A B : Set} {a1 a2 : A × B} → a1 ≡ a2 → proj₂ a1 ≡ proj₂ a2
pair-injective₂ refl = refl

-- substitution preserves well-formedness

substitution-preserves-wf* : ∀{es}{x}{e}
  → wf-e*₀ CT es
  → wf-e₀ CT e
  → wf-e*₀ CT (es [ x ↦ e ]*)
substitution-preserves-wf : ∀{e₀}{x}{e}
  → wf-e₀ CT e₀
  → wf-e₀ CT e
  → wf-e₀ CT (e₀ [ x ↦ e ])

substitution-preserves-wf {Var y}{x} wfe-e₀ wfe-e with x ≟ y
... | yes refl = wfe-e
... | no  x≢y  = tt
substitution-preserves-wf {Field e₀ f}{x} wfe-e₀ wfe-e =
  substitution-preserves-wf {e₀}{x} wfe-e₀ wfe-e
substitution-preserves-wf {Meth e₀ m es} (wfe-e₀ , wfe*-es) wfe-e =
  substitution-preserves-wf {e₀} wfe-e₀ wfe-e , substitution-preserves-wf* {es} wfe*-es wfe-e
substitution-preserves-wf {New C es} (wft-C , wfe*-es) wfe-e =
  wft-C , substitution-preserves-wf* {es} wfe*-es wfe-e
substitution-preserves-wf {Cast C e₀} (wft-C , wfe-e₀) wfe-e =
  wft-C , substitution-preserves-wf {e₀} wfe-e₀ wfe-e
substitution-preserves-wf {If e₀ e₁ e₂} (wfe-e₀ , wfe-e₁ , wfe-e₂) wfe-e =
  substitution-preserves-wf {e₀} wfe-e₀ wfe-e , substitution-preserves-wf {e₁} wfe-e₁ wfe-e , substitution-preserves-wf {e₂} wfe-e₂ wfe-e

substitution-preserves-wf* {[]} wfe*-es wfe-e = tt
substitution-preserves-wf* {e₀ ∷ es} (wfe-e₀ , wfe*-es) wfe-e =
  substitution-preserves-wf {e₀} wfe-e₀ wfe-e , substitution-preserves-wf* {es} wfe*-es wfe-e

-- simultaneous substitution preserves well-formedness

sim-subst-preserves-wf-var : ∀ x xs es
  → wf-e*₀ CT es
  → wf-e₀ CT (Var x [ xs ⤇ es ])
sim-subst-preserves-wf-var x [] [] wfe*-es = tt
sim-subst-preserves-wf-var x [] (x₁ ∷ es) wfe*-es = tt
sim-subst-preserves-wf-var x (x₁ ∷ xs) [] wfe*-es = tt
sim-subst-preserves-wf-var x (x₁ ∷ xs) (e ∷ es) (wfe-e , wfe*-es)
  with x ≟ x₁
... | yes refl = wfe-e
... | no _     = sim-subst-preserves-wf-var x xs es wfe*-es

sim-subst-preserves-wf* : ∀ {es₀}{xs} es
  → wf-e*₀ CT es₀
  → wf-e*₀ CT es
  → wf-e*₀ CT (es₀ [ xs ⤇ es ]*)
sim-subst-preserves-wf : ∀ {e₀}{xs} es
  → wf-e₀ CT e₀
  → wf-e*₀ CT es
  → wf-e₀ CT (e₀ [ xs ⤇ es ])
sim-subst-preserves-wf {Var x} {xs} es wfe-e₀ wfe*-es = sim-subst-preserves-wf-var x xs es wfe*-es
sim-subst-preserves-wf {Field e₀ f} {xs} es wfe-e₀ wfe*-es = sim-subst-preserves-wf {e₀} es wfe-e₀ wfe*-es
sim-subst-preserves-wf {Meth e₀ m ds} {xs} es (wfe-e₀ , wfe*-ds) wfe*-es =
  sim-subst-preserves-wf {e₀} es wfe-e₀ wfe*-es , sim-subst-preserves-wf* {ds} es wfe*-ds wfe*-es
sim-subst-preserves-wf {New C ds} {xs} es (wft-C , wfe*-ds) wfe*-es = wft-C , sim-subst-preserves-wf* {ds} es wfe*-ds wfe*-es
sim-subst-preserves-wf {Cast C e₀} {xs} es (wft-C , wfe-e₀) wfe*-es = wft-C , sim-subst-preserves-wf {e₀} es wfe-e₀ wfe*-es
sim-subst-preserves-wf {If e₀ e₁ e₂} {xs} es (wfe-e₀ , wfe-e₁ , wfe-e₂) wfe*-es =
  sim-subst-preserves-wf {e₀} es wfe-e₀ wfe*-es , sim-subst-preserves-wf {e₁} es wfe-e₁ wfe*-es , sim-subst-preserves-wf {e₂} es wfe-e₂ wfe*-es

sim-subst-preserves-wf* {[]} {xs} es wfe*-es₀ wfe*-es = tt
sim-subst-preserves-wf* {e₀ ∷ es₀} {xs} es (wfe-e₀ , wfe*-es₀) wfe*-es =
  sim-subst-preserves-wf {e₀} es wfe-e₀ wfe*-es , sim-subst-preserves-wf* es wfe*-es₀ wfe*-es

wf-select : ∀ {x} xs es e′
  → wf-e*₀ CT es
  → (xs ⤇ es) [ Bind.name ]∋ (x ⦂ e′)
  → wf-e₀ CT e′
wf-select [] [] e′ wfe*-es ()
wf-select [] (x ∷ es) e′ wfe*-es ()
wf-select (x ∷ xs) [] e′ wfe*-es ()
wf-select (x ∷ xs) (e ∷ es) .e (wfe-e , wfe*-es) (here x₂) = wfe-e
wf-select (x ∷ xs) (e ∷ es) e′ (wfe-e , wfe*-es) (there xe′∈ x₂) = wf-select xs es e′ wfe*-es xe′∈

-- reduction preserves well-formedness

wf-preservation* : ∀ {es}{es′}
  → wf-e*₀ CT es
  → es ⟶′ es′
  → wf-e*₀ CT es′

wf-preservation : ∀ {e}{e′}
  → wf-e₀ CT e
  → e ⟶ e′
  → wf-e₀ CT e′

wf-preservation (wft-C , wfe*-es) (R-Field {C} {es} {f}{fenv}{e} fields≡R f∈) =
  wf-select {f} (names fenv) es _ wfe*-es f∈ 
wf-preservation ((wft-C , wfe*-es) , wfe*-ds) (R-Invk  {C@ (Class cn)} {es} {m} {ds} {xs} {e₀} mbody≡R)
  with mlookup m C
wf-preservation ((wft-C , wfe*-es) , wfe*-ds) (R-Invk {C@(Class cn)} {es} {_} {ds} {xs} {.body} refl) | just arg@(cd , (method name ⦂ args ⇒ ty return body) , cd∈ , md∈)
  with dcls⇒wfm arg
... | (wf-arg-types , wf-res-type , wf-mbody)
  = sim-subst-preserves-wf {body} {"this" ∷ xs} (New C es ∷ ds) wf-mbody ((wft-C , wfe*-es) , wfe*-ds)
wf-preservation (wft-D , wft-C , wfe*-es) (R-Cast C<:D) = wft-C , wfe*-es
wf-preservation wfe-e (RC-Field {e₀}{e₀′}{f} e⟶e′) = wf-preservation wfe-e e⟶e′
wf-preservation (wfe-e , wfe*-es) (RC-Invk-Recv e⟶e′) = wf-preservation wfe-e e⟶e′ , wfe*-es
wf-preservation (wfe-e , wfe*-es) (RC-Invk-Arg es⟶es′) = wfe-e , wf-preservation* wfe*-es es⟶es′
wf-preservation (wft-C , wfe*-es) (RC-New-Arg es⟶es′) = wft-C , wf-preservation* wfe*-es es⟶es′
wf-preservation (wft-C , wfe-e) (RC-Cast e⟶e′) = wft-C , wf-preservation wfe-e e⟶e′

wf-preservation* (wfe-e , wfe*-es) (RC-here e⟶e′) = wf-preservation wfe-e e⟶e′ , wfe*-es
wf-preservation* (wfe-e , wfe*-es) (RC-there es⟶es′) = wfe-e , wf-preservation* wfe*-es es⟶es′

----------------------------------------------------------------------

wf-derivation : ∀ {Γ}{e}{T}
  → wf-t*₀ CT Γ
  → wf-e₀ CT e
  → Γ ⊢ e ⦂ T
  → wf-t₀ CT T
wf-derivation wft*-Γ wfe-e (T-Var x∈Γ) = wf-∈ wft*-Γ x∈Γ
wf-derivation wft*-Γ wfe-e (T-Field {e₀} {Object} {f} {.[]} {T} ⊢e refl ())
wf-derivation wft*-Γ wfe-e (T-Field {e₀} {Class cn} {f} {fenv} {T} ⊢e fields≡ f∈fenv)
  with height (Class cn)
wf-derivation wft*-Γ wfe-e (T-Field {_} {Class cn} {_} {fenv} {_} ⊢e () f∈fenv) | nothing
... | just n
  with getFields (suc n) (Class cn)
wf-derivation wft*-Γ wfe-e (T-Field {_} {Class cn} {_} {.fff} {_} ⊢e refl f∈fenv) | just n | fff , wft-fff = wf-∈ wft-fff f∈fenv
wf-derivation wft*-Γ wfe-e (T-Invk {e₀}{C₀}{m}{es}{margs}{T}{Ts} ⊢e mtype≡ ⊢*es Ts<:*)
  with mlookup m C₀
wf-derivation wft*-Γ wfe-e (T-Invk ⊢e refl ⊢*es Ts<:*) | just arg
  with dcls⇒wfm arg
... | _ , wft-res , _ = wft-res
wf-derivation wft*-Γ wfe-e (T-New fields≡ ⊢*es Ts<:*) = proj₁ wfe-e
wf-derivation wft*-Γ wfe-e (T-UCast ⊢e D<:T) = proj₁ wfe-e
wf-derivation wft*-Γ wfe-e (T-DCast ⊢e T<:D T≢D) = proj₁ wfe-e
wf-derivation wft*-Γ wfe-e (T-SCast ⊢e ¬T<:D ¬D<:T) = proj₁ wfe-e

------------------------------------------------------------
-- preliminary

weaken : ∀ {e}{T}{Γ} → [] ⊢ e ⦂ T → Γ ⊢ e ⦂ T
weaken* : ∀ {es}{Ts}{Γ} → [] ⊢* es ⦂ Ts → Γ ⊢* es ⦂ Ts

weaken (T-Field ⊢e x x₁) = T-Field (weaken ⊢e) x x₁
weaken (T-Invk ⊢e mtype≡ ⊢es Ts<:) = T-Invk (weaken ⊢e) mtype≡ (weaken* ⊢es) Ts<:
weaken (T-New fields≡ ⊢es Ts<:) = T-New fields≡ (weaken* ⊢es) Ts<:
weaken (T-UCast ⊢e x) = T-UCast (weaken ⊢e) x
weaken (T-DCast ⊢e x x₁) = T-DCast (weaken ⊢e) x x₁
weaken (T-SCast ⊢e x x₁) = T-SCast (weaken ⊢e) x x₁

weaken* [] = []
weaken* (⊢e ∷ ⊢*es) = weaken ⊢e ∷ weaken* ⊢*es

--------------------

substitution-preserves-typing* : ∀ {x}{U}{Γ}{es₀}{Ts₀}{e}{U′}
  → ((x ⦂ U) ∷ Γ) ⊢* es₀ ⦂ Ts₀
  → [] ⊢ e ⦂ U′
  → U′ <: U
  → ∃[ Ts₀′ ]( Ts₀′ <:* Ts₀ × Γ ⊢* es₀ [ x ↦ e ]* ⦂ Ts₀′ )

substitution-preserves-typing : ∀ {x}{U}{Γ}{e₀}{T₀}{e}{U′}
  → ((x ⦂ U) ∷ Γ) ⊢ e₀ ⦂ T₀
  → [] ⊢ e ⦂ U′
  → U′ <: U
  → ∃[ T₀′ ]( T₀′ <: T₀ × Γ ⊢ e₀ [ x ↦ e ] ⦂ T₀′ )
substitution-preserves-typing {x} (T-Var{y} y∈) ⊢e U′<:U with x ≟ y
substitution-preserves-typing {x} (T-Var {_} (here x₁)) ⊢e U′<:U | yes refl = _ , U′<:U , weaken ⊢e
substitution-preserves-typing {x} (T-Var {_} (there y∈ x≢x)) ⊢e U′<:U | yes refl = ⊥-elim (x≢x refl)
substitution-preserves-typing {x} (T-Var {_} (here x₁)) ⊢e U′<:U | no x≢y = ⊥-elim (x≢y refl)
substitution-preserves-typing {x} (T-Var {_} (there y∈ x₁)) ⊢e U′<:U | no x≢y = _ , S-Refl , T-Var y∈
substitution-preserves-typing (T-Field ⊢e₀ x x₁) ⊢e U′<:U
  with substitution-preserves-typing ⊢e₀ ⊢e U′<:U
... | T₀′ , T₀′<:C₀ , ⊢e₀′ = _ , (S-Refl , T-Field ⊢e₀′ {!  !} x₁)
substitution-preserves-typing (T-Invk ⊢e₀ x x₁ x₂) ⊢e U′<:U
  with substitution-preserves-typing ⊢e₀ ⊢e U′<:U | substitution-preserves-typing* x₁ ⊢e U′<:U
... | T₀′ , T₀′<:D , ⊢e₀′ | Ts′ , Ts′<:*Ts , ⊢es′ = _ , (S-Refl , (T-Invk ⊢e₀′ {!  !} ⊢es′ (s-trans* Ts′<:*Ts x₂)))
substitution-preserves-typing (T-New fields≡ ⊢es₀ Ts<:*) ⊢e U′<:U
  with substitution-preserves-typing* ⊢es₀ ⊢e U′<:U
... | Ts₀′ , Ts₀′<:Ts₀ , ⊢es₀′ = _ , S-Refl , T-New fields≡ ⊢es₀′ (s-trans* Ts₀′<:Ts₀ Ts<:*)
substitution-preserves-typing (T-UCast ⊢e₀ x) ⊢e U′<:U
  with substitution-preserves-typing ⊢e₀ ⊢e U′<:U
... | T₀′ , T₀′<:D , ⊢e₀′ = _ , (S-Refl , T-UCast ⊢e₀′ (S-Trans T₀′<:D x))
substitution-preserves-typing (T-DCast ⊢e₀ x x₁) ⊢e U′<:U
  with substitution-preserves-typing ⊢e₀ ⊢e U′<:U
... | T₀′ , T₀′<:D , ⊢e₀′ = _ , S-Refl , T-DCast ⊢e₀′ {!  !} {!   !} -- T₀ <: D × T₀ ≢ D → ∃A T₀ <: A × A <: D  
substitution-preserves-typing (T-SCast ⊢e₀ x x₁) ⊢e U′<:U
  with substitution-preserves-typing ⊢e₀ ⊢e U′<:U
... | T₀′ , T₀′<:D , ⊢e₀′ =  _ , (S-Refl , (T-SCast ⊢e₀′ (λ T₀<:Tₒ′ → x (S-Trans T₀<:Tₒ′ T₀′<:D)) λ T₀′<:T₀ → lemma-cd1 (lemma-cdd3 T₀′<:D T₀′<:T₀) x₁ x))

substitution-preserves-typing* [] ⊢e U′<:U = [] , S-Z , []
substitution-preserves-typing* (⊢e₀ ∷ ⊢es₀) ⊢e U′<:U
  with substitution-preserves-typing ⊢e₀ ⊢e U′<:U
     | substitution-preserves-typing* ⊢es₀ ⊢e U′<:U
...  | T₀′ , T₀′<:T₀ , ⊢e₀′
     | Ts₀′ , Ts₀′<:Ts₀ , ⊢es₀′ = (T₀′ ∷ Ts₀′) , S-S T₀′<:T₀ Ts₀′<:Ts₀ , ⊢e₀′ ∷ ⊢es₀′

-- revised for simultaneous substitution

subst-preserves-var : ∀ {Γ}{x₀}{T₀}{es}{Us′}
  → (∋x : Γ [ Bind.name ]∋ (x₀ ⦂ T₀))
  → [] ⊢* es ⦂ Us′
  → Us′ <:* map Bind.value Γ
  → ∃[ T₀′ ]( T₀′ <: T₀  ×  [] ⊢ Var x₀ [ map Bind.name Γ ⤇ es ] ⦂ T₀′ )
subst-preserves-var {Γ}{x₀}{T₀}{e ∷ es}(here x) (⊢e ∷ ⊢*es) (S-S T₀′<:T₀ Us′<*)
  with x₀ ≟ x₀
... | yes refl = _ , T₀′<:T₀ , ⊢e
... | no  x₀≢x₀ = ⊥-elim (x₀≢x₀ refl)
subst-preserves-var (there ∋x x) [] ()
subst-preserves-var {b ∷ Γ}{x₀} (there ∋x x₀≢bnb) (⊢e ∷ ⊢*es) (S-S _ Us′<*)
  with x₀ ≟ Bind.name b
... | yes x₀≡bnb = ⊥-elim (x₀≢bnb x₀≡bnb)
... | no _ = subst-preserves-var ∋x ⊢*es Us′<*

postulate
  proposed-lemma-0 : ∀ {C}{D}{fenv-c}
    → D <: C
    → fields C ≡ just fenv-c
    → ∃[ fenv-delta ] (fields D ≡ just (fenv-c ++ fenv-delta))

subst-preserves* : ∀ {Γ}{es₀}{Ts₀}{es}{Us′}
  → Γ ⊢* es₀ ⦂ Ts₀
  → [] ⊢* es ⦂ Us′
  → Us′ <:* map Bind.value Γ
  → ∃[ Ts₀′ ]( Ts₀′ <:* Ts₀  ×  [] ⊢* es₀ [ map Bind.name Γ ⤇ es ]* ⦂ Ts₀′ )

subst-preserves : ∀ {Γ}{e₀}{T₀}{es}{Us′}
  → Γ ⊢ e₀ ⦂ T₀
  → [] ⊢* es ⦂ Us′
  → Us′ <:* map Bind.value Γ
  → ∃[ T₀′ ]( T₀′ <: T₀  ×  [] ⊢ e₀ [ map Bind.name Γ ⤇ es ] ⦂ T₀′ )

subst-preserves (T-Var ∋x) ⊢*es Us′<* = subst-preserves-var ∋x ⊢*es Us′<*
subst-preserves {T₀ = T₀} (T-Field ⊢e₀ fields≡ fenv∋f) ⊢*es Us′<*
  with subst-preserves ⊢e₀ ⊢*es Us′<*
... | T₀′ , T₀′<:T₀ , ⊢e₀′
  with proposed-lemma-0 T₀′<:T₀ fields≡
... | fenv-delta , fields-T₀′≡ = T₀ , S-Refl , T-Field ⊢e₀′ fields-T₀′≡ (member-extension _ fenv∋f)
subst-preserves (T-Invk ⊢e₀ x x₁ x₂) ⊢*es Us′<*
  with subst-preserves ⊢e₀ ⊢*es Us′<* | subst-preserves* x₁ ⊢*es Us′<*
... | T₀′ , T₀′<:C₀ , ⊢e₀′ | Ts′ , Ts′<:*Ts , ⊢es′ = _ , S-Refl , T-Invk ⊢e₀′ {!  !} ⊢es′ (s-trans* Ts′<:*Ts x₂)
subst-preserves (T-New x x₁ x₂) ⊢*es Us′<*
  with subst-preserves* x₁ ⊢*es Us′<*
... | Ts′ , Ts′<:*Ts , ⊢es′ = _ , S-Refl , (T-New x ⊢es′ (s-trans* Ts′<:*Ts x₂))
subst-preserves (T-UCast ⊢e₀ x) ⊢*es Us′<*
  with subst-preserves ⊢e₀ ⊢*es Us′<*
... | T₀′ , T₀′<:D , ⊢e₀′ = _ , S-Refl , (T-UCast ⊢e₀′ (S-Trans T₀′<:D x))
subst-preserves (T-DCast ⊢e₀ x x₁) ⊢*es Us′<*
  with subst-preserves ⊢e₀ ⊢*es Us′<*
... | T₀′ , T₀′<:D , ⊢e₀′ = _ , S-Refl , (T-DCast ⊢e₀′ {!   !} {!   !})
subst-preserves (T-SCast ⊢e₀ x x₁) ⊢*es Us′<*
  with subst-preserves ⊢e₀ ⊢*es Us′<*
... | T₀′ , T₀′<:D , ⊢e₀′ = _ , S-Refl , T-SCast ⊢e₀′ (λ T₀<:T₀′ → x (S-Trans T₀<:T₀′ T₀′<:D)) λ T₀′<:T₀ → lemma-cd1 (lemma-cdd3 T₀′<:D T₀′<:T₀) x₁ x

subst-preserves* [] ⊢es Us′<:* = [] , S-Z , []
subst-preserves* (⊢e₀ ∷ ⊢es₀) ⊢es Us′<:*
  with subst-preserves ⊢e₀ ⊢es Us′<:* | subst-preserves* ⊢es₀ ⊢es Us′<:*
... | T₀ , T₀′<:T₀ , ⊢e₀′ | Ts₀ , Ts₀′<:Ts₀ , ⊢es₀′ = T₀ ∷ Ts₀ , S-S T₀′<:T₀ Ts₀′<:Ts₀ , ⊢e₀′ ∷ ⊢es₀′

------------------------------------------------------------

subject-reduction* : ∀ {Γ}{es es′}{Ts}
  → CLASSTABLE CT OK
  → wf-t*₀ CT Γ
  → wf-e*₀ CT es
  → Γ ⊢* es ⦂ Ts
  → es ⟶′ es′
  → ∃[ Ts′ ] (Ts′ <:* Ts × Γ ⊢* es′ ⦂ Ts′)

subject-reduction : ∀ {Γ}{e e′}{T}
  → CLASSTABLE CT OK
  → wf-t*₀ CT Γ
  → wf-e₀ CT e
  → Γ ⊢ e ⦂ T
  → e ⟶ e′
  → ∃[ T′ ] (T′ <: T × Γ ⊢ e′ ⦂ T′)

subject-reduction CT-ok wf-ctx wfe-e
                  (T-Field {e₀}{C₀}{f}{fenv}{T} (T-New {C} {es} {Ts} {flds} fields≡TN ⊢*es Ts<:*) fields≡TF f∈)
                  (R-Field fields≡R f∈fields)
  with flookup C₀
subject-reduction {Γ} CT-ok wf-ctx wfe-e
                  (T-Field {.(New C₀ _)} {C₀} {f} {fff} {T} (T-New {C₀} {es} {Ts} {.fff} refl ⊢*es Ts<:*) refl f∈)
                  (R-Field refl f∈fields) | just (fff , wft*-fff) = extract fff es Ts<:* ⊢*es f∈ f∈fields 
  where
    extract : ∀ {e′}{Ts} (fff : Fields) (es : List Exp) (Ts<:* : Ts <:* values fff) (⊢*es : Pointwise (_⊢_⦂_ Γ) es Ts)
      → fff [ Bind.name ]∋ (f ⦂ T) → (names fff ⤇ es) [ Bind.name ]∋ (f ⦂ e′) 
      → ∃[ T′ ] (T′ <: T × Γ ⊢ e′ ⦂ T′)
    extract [] [] S-Z [] () fe∈
    extract [] (x ∷ es) S-Z () ft∈ fe∈
    extract (x ∷ fff) [] (S-S x₁ Ts<:*) () ft∈ fe∈
    extract (.(f ⦂ T) ∷ fff) (e ∷ es) (S-S C<:T Ts<:*) (⊢e ∷ ⊢*es) (here x₂) (here x₃) = _ , C<:T , ⊢e
    extract (.(f ⦂ T) ∷ fff) (e ∷ es) (S-S C<:T Ts<:*) (⊢e ∷ ⊢*es) (here x₂) (there fe∈ f≢f) = ⊥-elim (f≢f refl)
    extract (bnd ∷ fff) (e ∷ es) (S-S C<:T Ts<:*) (⊢e ∷ ⊢*es) (there ft∈ x≢x) (here x₄) = ⊥-elim (x≢x refl)
    extract ((f′ ⦂ T′) ∷ fff) (e ∷ es) (S-S C<:T Ts<:*) (⊢e ∷ ⊢*es) (there ft∈ x₃) (there fe∈ x₄) = extract fff es Ts<:* ⊢*es ft∈ fe∈
subject-reduction CT-ok wf-ctx wfe-e
                  (T-Invk  {e₀}{Class cn}{m}{ds}{margs}{T}{Tds} (T-New {C} {es} {Tes} {flds} fields≡TN ⊢*es Ts<:*) mtype≡ ⊢*ds Ds<:*)
                  (R-Invk mbody≡)
  with mlookup m C
subject-reduction CT-ok wf-ctx wfe-e
                  (T-Invk {.(New (Class cn) _)} {Class cn} {_} {_} {.args} {T} {Tds} (T-New {.(Class cn)} {_} {Tes} {flds} fields≡TN ⊢*es Ts<:*) refl ⊢*ds Ds<:*)
                  (R-Invk refl)
                  | just (cd , (method name ⦂ args ⇒ ty return body) , cd∈ , md∈)
  with ⊢program⇒⊢class cd∈ CT-ok
... | T-Class refl ⊢mdecls
  with ⊢cd⇒⊢method {cd} md∈ ⊢mdecls
... | T-Method {E₀ = E₀} ⊢e₀ E₀<:C₀ refl _ = E₀ , E₀<:C₀ , {!⊢e₀!}
                  -- T , S-Refl , {!⊢program⇒⊢class!}
subject-reduction CT-ok wf-ctx wfe-e
                  (T-UCast (T-New {C} {es} {Ts} {flds} fields≡TN ⊢*es Ts<:*) C<:D₁)
                  (R-Cast C<:D) = C , C<:D , (T-New fields≡TN ⊢*es Ts<:*)
subject-reduction CT-ok wf-ctx wfe-e
                  (T-DCast (T-New {C} {es} {Ts} {flds} fields≡TN ⊢*es Ts<:*) D<:C D≢C)
                  (R-Cast C<:D) = ⊥-elim (D≢C (<:-antisymm D<:C C<:D))
subject-reduction CT-ok wf-ctx wfe-e
                  (T-SCast (T-New {C} {es} {Ts} {flds} fields≡TN ⊢*es Ts<:*) ¬D<:C ¬C<:D)
                  (R-Cast C<:D) = ⊥-elim (¬C<:D C<:D)
subject-reduction CT-ok wf-ctx wfe-e
                  (T-Field {e₀}{C₀}{f}{fenv}{T} ⊢e fields≡TF f∈)
                  (RC-Field e⟶e′)
  with subject-reduction CT-ok wf-ctx wfe-e ⊢e e⟶e′
... | T′ , T′<:C₀ , ⊢e′
  = T , S-Refl , T-Field{{!!}}{_}{T′}{f}{{!!}}{T} ⊢e′ {!!} {!!}
subject-reduction CT-ok wf-ctx wfe-e
                  ⊢e
                  (RC-Invk-Recv e⟶e′) = {!!}
subject-reduction CT-ok wf-ctx wfe-e
                  (T-Invk ⊢e mtype≡ ⊢*es Ts<:*)
                  (RC-Invk-Arg es⟶es′)
  with subject-reduction* CT-ok wf-ctx (proj₂ wfe-e) ⊢*es es⟶es′
... | Ts′ , Ts′<:Ts , ⊢*es′ = _ , S-Refl , T-Invk ⊢e mtype≡ ⊢*es′ (s-trans* Ts′<:Ts Ts<:*)
subject-reduction CT-ok wf-ctx wfe-e
                  (T-New {C} {es} {Ts} {flds} fields≡TN ⊢*es Ts<:*)
                  (RC-New-Arg es⟶es′)
  with subject-reduction* CT-ok wf-ctx (proj₂ wfe-e) ⊢*es es⟶es′
... | Ts′ , Ts′<:Ts , ⊢*es′ = _ , S-Refl , T-New fields≡TN ⊢*es′ (s-trans* Ts′<:Ts Ts<:*)
subject-reduction CT-ok wf-ctx wfe-e
                  (T-UCast ⊢e D<:T)
                  (RC-Cast e⟶e′)
  with subject-reduction CT-ok wf-ctx (proj₂ wfe-e) ⊢e e⟶e′
... | T′ , T′<:D , ⊢e′ = _ , S-Refl , T-UCast ⊢e′ (S-Trans T′<:D D<:T)
subject-reduction CT-ok wf-ctx wfe-e
                  (T-DCast {C}{D}{e₀} ⊢e C<:D C≢D)
                  (RC-Cast e⟶e′)
  with subject-reduction CT-ok wf-ctx (proj₂ wfe-e) ⊢e e⟶e′
... | T′ , T′<:D , ⊢e′
  with wf-preservation (proj₂ wfe-e) e⟶e′
... | wfe-e′
  with wf-derivation wf-ctx wfe-e′ ⊢e′
... | wft-T′
  with T′ [ wft-T′ ]<:? C
... | yes T′<:C = C , S-Refl , T-UCast ⊢e′ T′<:C
... | no ¬T′<:C
  with C [ proj₁ wfe-e ]<:? T′
... | no ¬C<:T′ = C , S-Refl , T-SCast ⊢e′ ¬C<:T′ ¬T′<:C
... | yes C<:T′ = C , S-Refl , T-DCast ⊢e′ C<:T′ (¬C<:D⇒C≢D ¬T′<:C ∘ sym)

subject-reduction {T = T} CT-ok wf-ctx wfe-e
                  (T-SCast ⊢e ¬T<:D ¬D<:T)
                  (RC-Cast e⟶e′)
  with wf-derivation wf-ctx (proj₂ wfe-e) ⊢e
... | wft-D
  with subject-reduction CT-ok wf-ctx (proj₂ wfe-e) ⊢e e⟶e′
... | D′ , D′<:D , ⊢e′ = _ , S-Refl , T-SCast ⊢e′ (lemma-cdd1 ¬T<:D D′<:D) ¬D′<:T
  where
    ¬D′<:T : ¬ D′ <: T
    ¬D′<:T D′<:T
      with lemma-cdd3 D′<:T D′<:D
    ... | inj₁ T<:D = ¬T<:D T<:D
    ... | inj₂ D<:T = ¬D<:T D<:T

subject-reduction* CT-ok wf-ctx wfe*-es (_∷_ {ys = Ts} ⊢e  ⊢*es) (RC-here e⟶e′)
  with subject-reduction CT-ok wf-ctx (proj₁ wfe*-es) ⊢e e⟶e′
... | T′ , T′<:T , ⊢e′ = T′ ∷ Ts , S-S T′<:T s-refl* , ⊢e′ ∷ ⊢*es

subject-reduction* CT-ok wf-ctx wfe*-es (_∷_ {y = T} ⊢e ⊢*es) (RC-there es⟶es′)
  with subject-reduction* CT-ok wf-ctx (proj₂ wfe*-es) ⊢*es es⟶es′
... | Ts′ , Ts′<:Ts , ⊢*es′ = T ∷ Ts′ , S-S S-Refl Ts′<:Ts , ⊢e ∷ ⊢*es′
