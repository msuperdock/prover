module Prover.Data.If where

open import Prover.Data.Bool
  using (Bool; false; true)
open import Prover.Data.Equal
  using (Equal; refl)
open import Prover.Data.Relation
  using (Decidable; no; yes)

import Data.If
  as If'

-- ## Definition

If
  = If'.If

-- ## Module

module If where

  open If'.If public

  -- ### Interface

  value
    : {A : Set}
    → If A true
    → A
  value (just x)
    = x

  -- ### Equality

  decidable
    : {A : Set}
    → {b : Bool}
    → Decidable (Equal A)
    → Decidable (Equal (If A b))
  decidable {b = false} _ nothing nothing
    = yes refl
  decidable {b = true} p (just x₁) (just x₂)
    with p x₁ x₂
  ... | no ¬q
    = no (λ {refl → ¬q refl})
  ... | yes refl
    = yes refl

-- ## Exports

open If public
  using (just; nothing)

