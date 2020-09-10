module Prover.Function.Partial.Sum where

open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

module _
  {A₁ A₂ B₁ B₂ : Set}
  where

  module PartialFunctionSum
    (F₁ : PartialFunction A₁ B₁)
    (F₂ : PartialFunction A₂ B₂)
    where

    base
      : A₁ ⊔ A₂
      → Maybe (B₁ ⊔ B₂)
    base (ι₁ x₁)
      = Maybe.map ι₁ (PartialFunction.base F₁ x₁)
    base (ι₂ x₂)
      = Maybe.map ι₂ (PartialFunction.base F₂ x₂)

  partial-function-sum
    : PartialFunction A₁ B₁
    → PartialFunction A₂ B₂
    → PartialFunction (A₁ ⊔ A₂) (B₁ ⊔ B₂)
  partial-function-sum F₁ F₂
    = record {PartialFunctionSum F₁ F₂}

