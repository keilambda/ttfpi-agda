module SystemF where

open import Data.String hiding (_++_) renaming (_≟_ to _s≟_)
open import Data.List
open import Data.List.Membership.DecPropositional _s≟_
open import Data.Sum
open import Relation.Nullary.Decidable

Name : Set
Name = String

data Kind : Set where
  * : Kind

infix  9 ``_
infixr 8 _⇒_
infix  5 Π_∶_,_

data Type : Set where
  ``_    : Name → Type
  _⇒_    : Type → Type → Type
  Π_∶_,_ : Name → Kind → Type → Type

FTV : Type → List Name
FTV (`` x) = [ x ]
FTV (A ⇒ B) = FTV A ++ FTV B
FTV (Π x ∶ α , A) = filter (λ v → ¬? (v s≟ x)) (FTV A)

type-subst : Type → Name → Type → Type
type-subst A@(`` x) x' Z with x s≟ x'
... | no  _ = A
... | yes _ = Z
type-subst (A ⇒ B) x Z = type-subst A x Z ⇒ type-subst B x Z
type-subst T@(Π α ∶ k , A) x Z = [ (λ _ → T) , (λ _ → Π α ∶ k , type-subst A x Z) ]
  (toSum (α s≟ x ⊎-dec α ∈? FTV Z))

infix  9 `_
infixr 5 ƛ_∶_⇒_
infixr 5 Λ_∶_⇒_
infixl 7 _·_
infixl 7 _□_

data Term : Set where
  `_     : Name → Term
  ƛ_∶_⇒_ : Name → Type → Term → Term -- (*, *)
  Λ_∶_⇒_ : Name → Kind → Term → Term -- (*, □)
  _·_    : Term → Term → Term
  _□_    : Term → Type → Term
