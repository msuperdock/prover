module Prover.Data.Text where

open import Prover.Data.Any
  using (Any)
open import Prover.Data.Char
  using (Char; _≟_char)
open import Prover.Data.Equal
  using (Equal)
open import Prover.Data.Function
  using (_$_)
open import Prover.Data.Nat
  using (_≟_nat)
open import Prover.Data.Relation
  using (Decidable)
open import Prover.Data.Vec
  using (Vec)

import Data.Text
  as Text'

-- ## Definition

Text
  = Text'.Text

-- ## Module

module Text where

  open Text'.Text public

  _≟_txt
    : Decidable (Equal Text)
  _≟_txt
    = Any.decidable (Vec Char) _≟_nat
    $ Vec.decidable _≟_char

-- ## Exports

open Text public
  using (_≟_txt)

