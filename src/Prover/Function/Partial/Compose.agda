module Prover.Function.Partial.Compose where

open import Prover.Category.Partial
  using (PartialFunctor; partial-functor-compose)
open import Prover.Category.Partial.Unit
  using (partial-functor-unit)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

partial-function-compose
  : {A B C : Set}
  → PartialFunction B C
  → PartialFunction A B
  → PartialFunction A C
partial-function-compose F G
  = PartialFunctor.partial-function
  $ partial-functor-compose
    (partial-functor-unit F)
    (partial-functor-unit G)

