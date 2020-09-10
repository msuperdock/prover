module Prover.Function.Partial.Product where

open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Product
  using (partial-functor-product)
open import Prover.Category.Partial.Unit
  using (partial-functor-unit)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

partial-function-product
  : {A₁ A₂ B₁ B₂ : Set}
  → PartialFunction A₁ B₁
  → PartialFunction A₂ B₂
  → PartialFunction (A₁ × A₂) (B₁ × B₂)
partial-function-product F₁ F₂
  = PartialFunctor.partial-function
  $ partial-functor-product
    (partial-functor-unit F₁)
    (partial-functor-unit F₂)

