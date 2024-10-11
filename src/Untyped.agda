module Untyped where

open import Data.String using (String)

Name : Set
Name = String

data Λ : Set where
  v : Name → Λ
  _·_ : Λ → Λ → Λ
  ƛ : Name → Λ → Λ
