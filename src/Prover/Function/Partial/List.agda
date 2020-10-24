module Prover.Function.Partial.List where

open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.List
  using (partial-functor-list)
open import Prover.Category.Partial.Unit
  using (partial-functor-unit)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

partial-function-list
  : {A B : Set}
  → PartialFunction A B
  → PartialFunction (List A) (List B)
partial-function-list F
  = PartialFunctor.partial-function
  $ partial-functor-list
    (partial-functor-unit F)

