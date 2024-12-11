module SystemF where

open import Data.String using (String)

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
