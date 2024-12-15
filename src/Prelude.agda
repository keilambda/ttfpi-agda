module Prelude where

open import Function.Bundles using (_⇔_; Equivalence)
open import Data.List using (List; _∷_; []; _++_; filter)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.String using (String)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Nullary using (¬?; ¬_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl; cong)

open Equivalence using (from; to; to-cong; from-cong)

record DecidableEq {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : DecidableEquality A

  infix 4 _≟_

open DecidableEq {{...}} public

instance
  DecidableEq-String : DecidableEq String
  DecidableEq-String = record { _≟_ = Data.String._≟_ }

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

∉-add : ∀ {ℓ A} {a : A} {s t : List {ℓ} A} → (a ∉ s ++ t) ⇔ (¬ (a ∈ s ⊎ a ∈ t))
∉-add .to m x   = m (∈-add .from x)
∉-add .from m x = m (∈-add .to x)
∉-add .to-cong   = cong (∉-add .to)
∉-add .from-cong = cong (∉-add .from)

_\\_ : {A : Set} → {{_ : DecidableEq A}} → List A → A → List A
xs \\ x = filter (λ y → ¬? (x ≟ y)) xs

infix 7 _\\_
