module Prover.Category.Partial.Simple where

open import Prover.Category.Partial
  using (PartialFunctor; partial-functor-compose)
open import Prover.Category.Partial.Unit
  using (partial-functor-unit)
open import Prover.Prelude

-- ## PartialFunction

-- ### Definition

PartialFunction
  : Set
  → Set
  → Set
PartialFunction A B
  = A → Maybe B

-- ### Compose

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

-- ## PartialDependentFunction

PartialDependentFunction
  : {A : Set}
  → (A → Set)
  → (A → Set)
  → Set
PartialDependentFunction {A = A} A' B'
  = (x : A)
  → A' x
  → Maybe (B' x)

