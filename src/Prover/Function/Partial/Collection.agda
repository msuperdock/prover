module Prover.Function.Partial.Collection where

open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Collection
  using (partial-functor-collection)
open import Prover.Category.Unit
  using (category-unit)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

partial-function-collection
  : {A : Set}
  → (R : Relation A)
  → Decidable R
  → PartialFunction (List A) (Collection R)
partial-function-collection {A = A} R d
  = PartialFunctor.base
  $ partial-functor-collection
    (category-unit A) R d

