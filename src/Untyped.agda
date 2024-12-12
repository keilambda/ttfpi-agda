module Untyped where

open import Function.Bundles using (_⇔_; Equivalence)
open import Data.List using (List; _∷_; []; [_]; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.String using (String)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product using (_×_)
open import Level using (zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; cong)

open import Data.List.Membership.Propositional using (_∈_)

open Equivalence using (from; to; to-cong; from-cong)

Name : Set
Name = String

-- 1.3.2: The set of all λ-terms
data Λ : Set where
  var : Name → Λ
  _·_ : Λ → Λ → Λ
  ƛ_⇒_ : Name → Λ → Λ

infixl 100 _·_

private
  variable
    L M N P Q R : Λ
    x y z u v w : Name

-- NOTE: Ideally should be implemented using a Multiset.
-- Alas, Agda does not support Quotient types out of the box and I am not smart enough for Cubical Agda yet.
Sub : Λ → List Λ
Sub (var x) = [ var x ]
Sub (M · N) = M · N ∷ Sub M ++ Sub N
Sub (ƛ x ⇒ M) = (ƛ x ⇒ M) ∷ Sub M

-- 1.3.5: Subterm
_⊆_ : Rel Λ zero
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
⊆-refl : M ⊆ M
⊆-refl {var x}   = here refl
⊆-refl {M · N}   = here refl
⊆-refl {ƛ x ⇒ M} = here refl

⊆-trans : L ⊆ M → M ⊆ N → L ⊆ N
⊆-trans {L} {M} {var x} lm (here refl) = lm
⊆-trans {L} {M} {P · Q} lm (here refl) = lm
⊆-trans {L} {M} {P · Q} lm (there mn) with ∈-add {s = Sub P} {t = Sub Q} .to mn
... | inl mp = there (∈-add .from (inl (⊆-trans lm mp)))
... | inr mq = there (∈-add .from (inr (⊆-trans lm mq)))
⊆-trans {L} {M} {ƛ x ⇒ Q} lm (here refl) = lm
⊆-trans {L} {M} {ƛ x ⇒ Q} lm (there mn) = there (⊆-trans lm mn)

-- 1.3.8: Proper subterm
_⊂_ : Rel Λ zero
L ⊂ M = L ≢ M × L ⊆ M
