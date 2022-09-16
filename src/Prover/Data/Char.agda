module Prover.Data.Char where

open import Prover.Data.Bool
  using (Bool)
open import Prover.Data.Equal
  using (Equal; refl)
open import Prover.Data.Nat
  using (_≟_nat)
open import Prover.Data.Relation
  using (Dec; Decidable; no; yes)

import Agda.Builtin.Char
  as Builtin
import Agda.Builtin.Char.Properties
  as Properties
import Data.Char
  as Char'

open Builtin
  using () renaming
  ( primCharToNat
    to to-nat
  )

open Properties
  using () renaming
  ( primCharToNatInjective
    to to-nat-injective
  )

-- ## Definition

Char
  = Char'.Char

-- ## Module

module Char where

  open Char'.Char public

  -- ### Equality

  _≟_char
    : Decidable (Equal Char)
  c₁ ≟ c₂ char
    with to-nat c₁ ≟ to-nat c₂ nat
  ... | no ¬p
    = no (λ {refl → ¬p refl})
  ... | yes p
    = yes (Equal.from-builtin (to-nat-injective c₁ c₂ (Equal.to-builtin p)))

  -- ### Conversion

  is-digit?
    : (c : Char)
    → Dec (IsDigit c)
  is-digit? c
    = Bool.to-dec (is-digit c)

-- ## Exports

open Char public
  using (_≟_char)

