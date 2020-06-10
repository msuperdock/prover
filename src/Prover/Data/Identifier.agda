module Prover.Data.Identifier where

open import Prover.Prelude

open import Prover.Data.Text public using () renaming
  ( Text
    to Identifier
  )

_≟_idn
  : Decidable Identifier
_≟_idn
  = Any.decidable _≟_nat (Vec.decidable _≟_char)

