{-# OPTIONS --allow-unsolved-metas #-}

module STLC where

open import Data.String using (String) renaming (_≟_ to _s≟_)
open import Data.List using (List; [_]; _++_; filter)
open import Data.Product.Base using (_×_; _,_; ∃; ∃-syntax; proj₂)
open import Function.Base using (case_of_)
open import Function.Bundles using (_⇔_; Equivalence)
open import Relation.Nullary using (Dec; yes; no; ¬?; contradiction)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; ≢-sym)

open Equivalence using (from; to; to-cong; from-cong)

Name : Set
Name = String

infix  9 ``_
infixr 8 _⇒_

data Type : Set where
  ``_ : Name → Type
  _⇒_ : Type → Type → Type

⇒-cong₁ : ∀ {A B C} → A ≡ B → A ⇒ C ≡ B ⇒ C
⇒-cong₁ refl = refl

⇒-cong₂ : ∀ {A B C} → A ≡ B → C ⇒ A ≡ C ⇒ B
⇒-cong₂ refl = refl

⇒-inj₁ : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → A ≡ C
⇒-inj₁ refl = refl

⇒-inj₂ : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → B ≡ D
⇒-inj₂ refl = refl

``≢⇒ : ∀ {A B x} → `` x ≢ A ⇒ B
``≢⇒ ()

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
  here  : ∀ {Γ x A} → Γ , x ∶ A ∋ x ∶ A
  there : ∀ {Γ x y A B}
    → x ≢ y
    -----------
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

Typeable : Term → Set
Typeable M = ∃[ Γ ] ∃[ A ] Γ ⊢ M ∶ A

TypeFinding : Context → Term → Set
TypeFinding Γ M = ∃[ A ] Γ ⊢ M ∶ A

TermFinding : Context → Type → Set
TermFinding Γ A = ∃[ M ] Γ ⊢ M ∶ A

TypeChecking : Context → Term → Type → Set
TypeChecking Γ M A = Γ ⊢ M ∶ A

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

_≟_ : DecidableEquality Type
(`` x) ≟ (`` y) with x s≟ y
... | yes refl = yes refl
... | no n     = no λ{refl → n refl}
(`` x) ≟ (A ⇒ B) = no λ()
(A ⇒ B) ≟ (`` x) = no λ()
(A ⇒ B) ≟ (A’ ⇒ B’) with A ≟ A’ | B ≟ B’
... | no na    | _        = no λ{refl → na refl}
... | yes _    | no nb    = no λ{refl → nb refl}
... | yes refl | yes refl = yes refl

uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ∶ A → Γ ∋ x ∶ B → A ≡ B
uniq-∋ here here               = refl
uniq-∋ here (there nx _)       = contradiction refl nx
uniq-∋ (there nx _) here       = contradiction refl nx
uniq-∋ (there _ x) (there _ y) = uniq-∋ x y

uniq : ∀ {Γ M A B} → Γ ⊢ M ∶ A → Γ ⊢ M ∶ B → A ≡ B
uniq (⊢` ∋x) (⊢` ∋y)       = uniq-∋ ∋x ∋y
uniq (⊢ƛ MA) (⊢ƛ MB)       = ⇒-cong₂ (uniq MA MB)
uniq (⊢ MA · _) (⊢ MB · _) = ⇒-inj₂ (uniq MA MB)

ext-∋ : ∀ {Γ x y B}
  → x ≢ y
  → ¬ (∃[ A ] Γ ∋ x ∶ A)
  → ¬ (∃[ A ] Γ , y ∶ B ∋ x ∶ A)
ext-∋ x≢y _ (_ , here)       = contradiction refl x≢y
ext-∋ _  ¬∃ (A , there _ ∋x) = ¬∃ (A , ∋x)

lookup : ∀ Γ x → Dec (∃[ A ] Γ ∋ x ∶ A)
lookup ∅ x = no λ()
lookup (Γ , y ∶ B) x with x s≟ y
... | yes refl = yes (B , here)
... | no nx with lookup Γ x
...   | yes (A , x) = yes (A , there nx x)
...   | no nex      = no (ext-∋ nx nex)

type-infer : ∀ Γ M → Dec (∃[ A ] Γ ⊢ M ∶ A)
type-infer Γ (` x) with lookup Γ x
... | no ¬∃        = no λ { (A , (⊢` ∋x)) → ¬∃ (A , ∋x) }
... | yes (A , ∋x) = yes (A , (⊢` ∋x))
type-infer Γ (ƛ x ∶ A ⇒ M) with type-infer (Γ , x ∶ A) M
... | no ¬MB       = no λ { (_ ⇒ B , (⊢ƛ MB)) → ¬MB (B , MB) }
... | yes (B , MB) = yes (A ⇒ B , (⊢ƛ MB))
type-infer Γ (M · N) with type-infer Γ M | type-infer Γ N
... | no _    | no ¬NA  = no λ { (_ , ⊢ _ · NA) → ¬NA (_ , NA) }
... | yes _   | no ¬NA  = no λ { (_ , ⊢ _ · NA) → ¬NA (_ , NA) }
... | no ¬MAB | yes _   = no λ { (_ , ⊢ MAB · _) → ¬MAB (_ , MAB) }
... | yes (`` _ ,  MA)  | yes _ = no λ { (_ , (⊢ MAB · _)) → contradiction (uniq MA MAB) ``≢⇒ }
... | yes (A ⇒ B , MAB) | yes (A' , NA') with A ≟ A'
...   | no A≢A' = no λ { (_ , (⊢ MA''B · NA'')) → A≢A' (trans (⇒-inj₁ (uniq MAB MA''B)) (uniq NA'' NA')) }
...   | yes refl = yes (B , ⊢ MAB · NA')

type-check : ∀ Γ M A → Dec (Γ ⊢ M ∶ A)
-- var
type-check Γ (` x) A with lookup Γ x
... | no ¬∃ = no λ xA → ¬∃ (A , `-gen .to xA)
... | yes (A’ , ∋x) with A’ ≟ A
...   | yes refl = yes (⊢` ∋x)
...   | no A’≢A  = no λ xA → A’≢A (uniq-∋ ∋x (`-gen .to xA))
-- abs
type-check Γ (ƛ x ∶ A’ ⇒ M) (`` B) = no λ()
type-check Γ (ƛ x ∶ A’ ⇒ M) (A ⇒ B) with A’ ≟ A
... | no  A’≢A = no λ{ (⊢ƛ _) → A’≢A refl }
... | yes refl with type-check (Γ , x ∶ A) M B
...   | no ¬MB = no λ { (⊢ƛ MB) → ¬MB MB }
...   | yes MB = yes (⊢ƛ MB)
-- app
type-check Γ (` x · N) B with lookup Γ x
... | no ¬∃           = no λ { (⊢ MAB · _) → ¬∃ (_ , `-gen .to MAB) }
... | yes (`` y , MA) = no λ { (⊢ MAB · NA) → contradiction (uniq-∋ (`-gen .to MAB) MA) (≢-sym ``≢⇒) }
... | yes (A ⇒ B’ , MAB’) with B ≟ B’
...   | no B≢B’ = no λ { (⊢ MAB · _) → B≢B’ (⇒-inj₂ (uniq-∋ (`-gen .to MAB) MAB’)) }
...   | yes refl with type-check Γ N A
...     | no ¬NA = no λ { (⊢ MA’B · NA’) → ¬NA (case (⇒-inj₁ (uniq-∋ (`-gen .to MA’B) MAB’)) of λ { refl → NA’ }) }
...     | yes NA = yes (⊢ ⊢` MAB’ · NA)
type-check Γ ((ƛ x ∶ A ⇒ M) · N) B with type-check (Γ , x ∶ A) M B
... | no ¬MB = no λ { (⊢ MA’B · _) → case ƛ-gen .to MA’B of λ { (_ , MB , refl) → ¬MB MB } }
... | yes MB with type-check Γ N A
...   | no ¬NA = no λ { (⊢ MA’B · NA) → ¬NA (case ⇒-inj₁ (proj₂ (proj₂ (ƛ-gen .to MA’B))) of λ { refl → NA }) }
...   | yes NA = yes (⊢ ⊢ƛ MB · NA)
type-check Γ (L · M · N) B = {!   !}
