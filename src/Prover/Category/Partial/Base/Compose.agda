module Prover.Category.Partial.Base.Compose where

open import Prover.Category.Partial
  using (PartialFunctor; partial-functor-compose)
open import Prover.Category.Partial.Base
  using (PartialFunction)
open import Prover.Category.Partial.Unit
  using (partial-functor-unit)
open import Prover.Prelude

partial-function-compose
  : {A B C : Set}
  → PartialFunction B C
  → PartialFunction A B
  → PartialFunction A C
partial-function-compose f g
  = PartialFunctor.base
  $ partial-functor-compose
    (partial-functor-unit f)
    (partial-functor-unit g)

