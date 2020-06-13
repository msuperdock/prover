module Prover.Category.Partial.Simple.Product where

open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Product
  using (partial-functor-product)
open import Prover.Category.Partial.Simple
  using (PartialFunction)
open import Prover.Category.Partial.Unit
  using (partial-functor-unit)
open import Prover.Prelude

-- ## PartialFunction

partial-function-product
  : {A₁ A₂ B₁ B₂ : Set}
  → PartialFunction A₁ B₁
  → PartialFunction A₂ B₂
  → PartialFunction (A₁ × A₂) (B₁ × B₂)
partial-function-product f₁ f₂
  = PartialFunctor.base
  $ partial-functor-product
    (partial-functor-unit f₁)
    (partial-functor-unit f₂)

