module Prover.Data.Meta where

open import Prover.Data.Nat
  using (module Nat; ℕ)

-- ## Definition

Meta
  : Set
Meta
  = ℕ

-- ## Module

module Meta where

  open Nat public
    using () renaming
    ( _≟_nat
      to _≟_met
    )

-- ## Exports

open Meta public
  using (_≟_met)

