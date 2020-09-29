module Prover.Function.Bool where

open import Prover.Prelude

-- ## BoolFunction

BoolFunction
  : Set
  → Set
BoolFunction A
  = A
  → Bool

