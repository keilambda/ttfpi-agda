module Untyped where

open import Data.Nat using (ℕ; _+_; _<_; s≤s; z≤n)
open import Data.String.Base using (String; _++_)

Name : Set
Name = String

data Λ : Set where
  var : Name → Λ
  _·_ : Λ → Λ → Λ
  ƛ_⇒_ : Name → Λ → Λ

infixl 100 _·_

private
  variable
    L M N P Q R : Λ
    x y z u v w : Name

show : Λ → String
show (var x) = x
show (M · N) = "(" ++ show M ++ " " ++ show N ++ ")"
show (ƛ x ⇒ M) = "(λ" ++ x ++ ". " ++ show M ++ ")"

∣_∣ : Λ → ℕ
∣ var x ∣ = 1
∣ M · N ∣ = 1 + ∣ M ∣ + ∣ N ∣
∣ ƛ x ⇒ M ∣ = 1 + ∣ M ∣

z<∣M∣ : 0 < ∣ M ∣
z<∣M∣ {var x} = s≤s z≤n
z<∣M∣ {M · N} = s≤s z≤n
z<∣M∣ {ƛ x ⇒ M} = s≤s z≤n
