module Prover.Data.Identifier where

open import Prover.Data.Text public using () renaming
  ( Text
    to Identifier
  ; _≟_txt
    to _≟_idn
  )

