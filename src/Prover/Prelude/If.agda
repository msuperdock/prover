module Prover.Prelude.If where

open import Prover.Prelude.Bool
  using (Bool; false; true)
open import Prover.Prelude.Decidable
  using (Decidable; no; yes)
open import Prover.Prelude.Equality
  using (refl)

-- ## Definition

module _If where

  data If
    (A : Set)
    : Bool
    → Set
    where
  
    nothing
      : If A false
  
    just
      : A
      → If A true

If
  : Set
  → Bool
  → Set
If
  = _If.If

open _If.If public

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
    → Decidable A
    → Decidable (If A b)
  decidable {b = false} _ nothing nothing
    = yes refl
  decidable {b = true} p (just x₁) (just x₂)
    with p x₁ x₂
  ... | no ¬q
    = no (λ {refl → ¬q refl})
  ... | yes refl
    = yes refl

