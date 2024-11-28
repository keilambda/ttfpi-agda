module Untyped where

open import Data.Nat using (ℕ; _+_; _<_; s≤s; z≤n)
open import Data.List using (List; _∷_; [_]; _++_)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Level using (zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Data.List.Membership.Propositional using (_∈_)

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

∣_∣ : Λ → ℕ
∣ var x ∣ = 1
∣ M · N ∣ = 1 + ∣ M ∣ + ∣ N ∣
∣ ƛ x ⇒ M ∣ = 1 + ∣ M ∣

z<∣M∣ : 0 < ∣ M ∣
z<∣M∣ {var x} = s≤s z≤n
z<∣M∣ {M · N} = s≤s z≤n
z<∣M∣ {ƛ x ⇒ M} = s≤s z≤n

-- NOTE: Ideally should be implemented using a Multiset.
-- Alas, Agda does not support Quotient types out of the box and I am not smart enough for Cubical Agda yet.
Sub : Λ → List Λ
Sub (var x) = [ var x ]
Sub (M · N) = M · N ∷ Sub M ++ Sub N
Sub (ƛ x ⇒ M) = (ƛ x ⇒ M) ∷ Sub M

-- 1.3.5: Subterm
_⊆_ : Rel Λ zero
L ⊆ M = L ∈ Sub M

-- 1.3.8: Proper subterm
_⊂_ : Rel Λ zero
L ⊂ M = L ≢ M × L ⊆ M
