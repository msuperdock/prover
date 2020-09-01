module Prover.Function.Partial where

open import Prover.Prelude

-- ## PartialFunction

PartialFunction
  : Set
  → Set
  → Set
PartialFunction A B
  = A
  → Maybe B

