module Prover.Client.Event where

open import Prover.Prelude

data SpecialEvent
  : Set
  where

  escape
    : SpecialEvent

  return
    : SpecialEvent

  direction
    : Direction
    → SpecialEvent
