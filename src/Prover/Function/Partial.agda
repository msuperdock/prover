module Prover.Function.Partial where

open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Prelude

-- ## PartialFunction

PartialFunction
  : Set
  → Set
  → Set
PartialFunction A B
  = A
  → Maybe B

module PartialFunction where

  bool-function
    : {A B : Set}
    → PartialFunction A B
    → BoolFunction A
  bool-function f x
    = Maybe.is-just (f x)

