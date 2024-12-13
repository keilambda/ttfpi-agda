module Untyped where

open import Function.Bundles using (_⇔_; Equivalence)
open import Data.Bool using (if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; []; [_]; _++_; filter)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.String using (String; _≟_)
open import Data.Sum using (_⊎_; [_,_]) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product using (_×_)
open import Level using (zero)
open import Relation.Nullary using (Dec; yes; no; ¬?; toSum; _⊎-dec_; ⌊_⌋)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.DecPropositional (_≟_) using (_∈?_)

open Equivalence using (from; to; to-cong; from-cong)

Name : Set
Name = String

-- 1.3.2: The set of all λ-terms
data Term : Set where
  var  : Name → Term
  _·_  : Term → Term → Term
  ƛ_⇒_ : Name → Term → Term

infixl 7 _·_
infixr 5 ƛ_⇒_

-- NOTE: Ideally should be implemented using a Multiset.
-- Alas, Agda does not support Quotient types out of the box and I am not smart enough for Cubical Agda yet.
Sub : Term → List Term
Sub (var x) = [ var x ]
Sub (M · N) = M · N ∷ Sub M ++ Sub N
Sub (ƛ x ⇒ M) = (ƛ x ⇒ M) ∷ Sub M

-- 1.3.5: Subterm
_⊆_ : Rel Term zero
L ⊆ M = L ∈ Sub M

∈-add : ∀ {ℓ A} {a : A} {s t : List {ℓ} A} → (a ∈ s ++ t) ⇔ (a ∈ s ⊎ a ∈ t)
∈-add {s = []}     .to x = inr x
∈-add {s = s ∷ ss} .to (here refl) = inl (here refl)
∈-add {s = s ∷ ss} .to (there x) with ∈-add {s = ss} .to x
... | inl q = inl (there q)
... | inr q = inr q
∈-add {s = []}     .from (inr x) = x
∈-add {s = s ∷ ss} .from (inl (here refl)) = here refl
∈-add {s = s ∷ ss} .from (inl (there x)) = there (∈-add .from (inl x))
∈-add {s = s ∷ ss} .from (inr x) = there (∈-add .from (inr x))
∈-add .to-cong   = cong (∈-add .to)
∈-add .from-cong = cong (∈-add .from)

-- 1.3.6: Subterm relation is reflexive and transitive
⊆-refl : ∀ {M} → M ⊆ M
⊆-refl {var x}   = here refl
⊆-refl {M · N}   = here refl
⊆-refl {ƛ x ⇒ M} = here refl

⊆-trans : ∀ {L M N} → L ⊆ M → M ⊆ N → L ⊆ N
⊆-trans {L} {M} {var x} lm (here refl) = lm
⊆-trans {L} {M} {P · Q} lm (here refl) = lm
⊆-trans {L} {M} {P · Q} lm (there mn) with ∈-add {s = Sub P} {t = Sub Q} .to mn
... | inl mp = there (∈-add .from (inl (⊆-trans lm mp)))
... | inr mq = there (∈-add .from (inr (⊆-trans lm mq)))
⊆-trans {L} {M} {ƛ x ⇒ Q} lm (here refl) = lm
⊆-trans {L} {M} {ƛ x ⇒ Q} lm (there mn) = there (⊆-trans lm mn)

-- 1.3.8: Proper subterm
_⊂_ : Rel Term zero
L ⊂ M = L ≢ M × L ⊆ M

-- 1.4.1: The set of free variables of a λ-term
FV : Term → List Name
FV (var x) = [ x ]
FV (ƛ x ⇒ M) = filter (λ y → ¬? (x ≟ y)) (FV M)
FV (M · N) = FV M ++ FV N

-- 1.4.3: Closed λ-term; combinator; Λ⁰
Closed : Term → Set
Closed M = FV M ≡ []

-- 1.5.1: Renaming
_binding-∈_ : Name → Term → Set
x binding-∈ var _   = ⊥
x binding-∈ M · N   = x binding-∈ M ⊎ x binding-∈ N
x binding-∈ ƛ y ⇒ M = x ≡ y ⊎ x binding-∈ M

infix 4 _binding-∈_

_binding-∉_ : Name → Term → Set
x binding-∉ M = ¬ x binding-∈ M

infix 4 _binding-∉_

_binding-∈?_ : (x : Name) → (M : Term) → Dec (x binding-∈ M)
x binding-∈? var _ = no λ()
x binding-∈? (M · N) with x binding-∈? M | x binding-∈? N
... | yes xM | _      = yes (inl xM)
... | _      | yes xN = yes (inr xN)
... | no ¬xM | no ¬xN = no λ { (inl xM) → ¬xM xM ; (inr xN) → ¬xN xN }
x binding-∈? (ƛ y ⇒ M) with x ≟ y
... | yes refl = yes (inl refl)
... | no x≢y with x binding-∈? M
...   | yes xM = yes (inr xM)
...   | no ¬xM = no λ { (inl x≡y) → x≢y x≡y ; (inr xM) → ¬xM xM }

infix 4 _binding-∈?_

_[_↦_] : Term → Name → Name → Term
t@(var z) [ x ↦ y ] with x ≟ z
... | yes _ = var y
... | no  _ = t
(M · N) [ x ↦ y ] = (M [ x ↦ y ]) · (N [ x ↦ y ])
t@(ƛ z ⇒ M) [ x ↦ y ] =
  [ (λ _ → t)
  , (λ _ → if ⌊ z ≟ x ⌋ then ƛ y ⇒ (M [ x ↦ y ]) else ƛ z ⇒ (M [ x ↦ y ]))
  ] (toSum (y binding-∈? M ⊎-dec y ∈? FV M))

infix 8 _[_↦_]

data Renaming : Rel Term zero where
  rename : ∀ {x y M} → y ∉ FV M → y binding-∉ M → Renaming (ƛ x ⇒ M) (ƛ y ⇒ M [ x ↦ y ])

-- 1.5.2: α-conversion or α-equivalence; =α
data _≡α_ : Rel Term zero where
  α-rename : ∀ {M N} → Renaming M N → M ≡α N
  α-appl : ∀ {L M N} → M ≡α N → (M · L) ≡α (N · L)
  α-appr : ∀ {L M N} → M ≡α N → (L · M) ≡α (L · N)
  α-abst : ∀ {z M N} → M ≡α N → (ƛ z ⇒ M) ≡α (ƛ z ⇒ N)
  α-refl : ∀ {M} → M ≡α M
  α-sym : ∀ {M N} → M ≡α N → N ≡α M
  α-trans : ∀ {L M N} → L ≡α M → M ≡α N → L ≡α N

infix 4 _≡α_

-- 1.5.4: α-variant
AlphaVariant : Rel Term zero
AlphaVariant = _≡α_

-- 1.6.1: Substitution
_[_:=_] : Term → Name → Term → Term
T@(var y) [ x := N ] with x ≟ y
... | no  _ = T
... | yes _ = N
(M · L) [ x := N ] = M [ x := N ] · L [ x := N ]
T@(ƛ y ⇒ M) [ x := N ] =
  [ (λ _ → T)
  , (λ _ → ƛ y ⇒ M [ x := N ])
  ] (toSum (x ≟ y ⊎-dec y ∈? FV N))

infix 9 _[_:=_]
