module Prover.Function.Partial where

open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Prelude

-- ## PartialFunction

record PartialFunction
  (A B : Set)
  : Set
  where

  constructor

    partial-function

  field

    base
      : A
      → Maybe B

  bool-function
    : BoolFunction A
  bool-function x
    = Maybe.is-just (base x)

