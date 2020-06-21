module Prover.Client.Event where

open import Prover.Prelude

data SpecialEvent
  : Set
  where

  quit
    : SpecialEvent

  write
    : SpecialEvent

  escape
    : SpecialEvent

  return
    : SpecialEvent

  direction
    : Direction
    → SpecialEvent

