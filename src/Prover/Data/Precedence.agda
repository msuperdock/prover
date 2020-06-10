module Prover.Data.Precedence where

open import Prover.Prelude

-- ## Definition

Precedence
  : Set
Precedence
  = ℕ

-- ## Module

module Precedence where

  open Nat public
    using (compare; transitive)

  open Nat public using () renaming
    ( _≟_nat
      to _≟_prc
    ; _<_nat
      to _<_prc
    )

-- ## Exports

open Precedence public
  using (_≟_prc; _<_prc)

