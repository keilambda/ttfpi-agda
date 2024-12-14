module Prelude where

open import Data.String using (String)
open import Relation.Binary.Definitions using (DecidableEquality)

record DecidableEq {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : DecidableEquality A

  infix 4 _≟_

open DecidableEq {{...}} public

instance
  DecidableEq-String : DecidableEq String
  DecidableEq-String = record { _≟_ = Data.String._≟_ }
