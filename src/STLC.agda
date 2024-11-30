open import Data.String using (String) renaming (_≟_ to _s≟_)
open import Data.List using (List; _∷_; []; [_]; _++_; filter)
open import Data.Product.Base using (_×_; _,_; ∃; ∃-syntax)
open import Function.Bundles using (_⇔_; Equivalence)
open import Relation.Nullary using (Dec; yes; no; ¬?)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)

open import Data.List.Membership.Propositional using (_∈_)

open Equivalence using (from; to; to-cong; from-cong)

Name : Set
Name = String

infix  9 ``_
infixr 8 _⇒_

data Type : Set where
  ``_ : Name → Type
  _⇒_ : Type → Type → Type

infixr 5 ƛ_∶_⇒_
infixl 7 _·_
infix  9 `_

data Term : Set where
  `_     : Name → Term
  ƛ_∶_⇒_ : Name → Type → Term → Term
  _·_    : Term → Term → Term

FV : Term → List Name
FV (` x) = [ x ]
FV (ƛ x ∶ A ⇒ M) = filter (λ y → ¬? (x s≟ y)) (FV M)
FV (M · N) = FV M ++ FV N

infixl 5 _,_∶_

data Context : Set where
  ∅     : Context
  _,_∶_ : Context → Name → Type → Context

infix 4 _∋_∶_

data _∋_∶_ : Context → Name → Type → Set where
  Z : ∀ {Γ x A}
    -------------------
    → Γ , x ∶ A ∋ x ∶ A

  S : ∀ {Γ x y A B}
    → Γ ∋ x ∶ A
    -------------------
    → Γ , y ∶ B ∋ x ∶ A

infix 4 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where
  ⊢`_ : ∀ {Γ x A}
    → Γ ∋ x ∶ A
    -------------
    → Γ ⊢ ` x ∶ A

  ⊢ƛ_ : ∀ {Γ x A B M}
    → Γ , x ∶ A ⊢ M ∶ B
    -----------------------------
    → Γ ⊢ (ƛ x ∶ A ⇒ M) ∶ (A ⇒ B)

  ⊢_·_ : ∀ {Γ A B M N}
    → Γ ⊢ M ∶ (A ⇒ B)
    -----------------
    → Γ ⊢ N ∶ A
    -----------------
    → Γ ⊢ (M · N) ∶ B

infix 4 ⊢_∶_

⊢_∶_ : Term → Type → Set
⊢ M ∶ A = ∅ ⊢ M ∶ A

Typeable : Term → Set
Typeable M = ∃[ A ] ⊢ M ∶ A

`-gen : ∀ {Γ x A} → (Γ ⊢ ` x ∶ A) ⇔ (Γ ∋ x ∶ A)
`-gen .to (⊢` x) = x
`-gen .from x = ⊢` x
`-gen .to-cong = cong (`-gen .to)
`-gen .from-cong = cong (`-gen .from)

·-gen : ∀ {Γ M N B} → (Γ ⊢ (M · N) ∶ B) ⇔ (∃[ A ] (Γ ⊢ M ∶ (A ⇒ B)) × (Γ ⊢ N ∶ A))
·-gen .to (⊢ M · N) = _ , M , N
·-gen .from (_ , M , N) = ⊢ M · N
·-gen .to-cong = cong (·-gen .to)
·-gen .from-cong = cong (·-gen .from)

ƛ-gen : ∀ {Γ x A C M} → (Γ ⊢ (ƛ x ∶ A ⇒ M) ∶ C) ⇔ (∃[ B ] (((Γ , x ∶ A) ⊢ M ∶ B) × (C ≡ (A ⇒ B))))
ƛ-gen .to (⊢ƛ M) = _ , M , refl
ƛ-gen .from (_ , M , refl) = ⊢ƛ M
ƛ-gen .to-cong = cong (ƛ-gen .to)
ƛ-gen .from-cong = cong (ƛ-gen .from)
