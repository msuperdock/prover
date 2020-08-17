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

