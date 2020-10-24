module Prover.Prelude.If where

open import Prover.Prelude.Bool
  using (Bool; false; true)
open import Prover.Prelude.Equal
  using (Equal; refl)
open import Prover.Prelude.Relation
  using (Decidable; no; yes)

-- ## Definition

data If'
  (A : Set)
  : Bool
  → Set
  where

  nothing
    : If' A false

  just
    : A
    → If' A true

If
  = If'

-- ## Module

module If where

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

