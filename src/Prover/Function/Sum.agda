module Prover.Function.Sum where

open import Prover.Function
  using (Function)
open import Prover.Prelude

-- ## Function

module _
  {A₁ A₂ B₁ B₂ : Set}
  where

  module FunctionSum
    (F₁ : Function A₁ B₁)
    (F₂ : Function A₂ B₂)
    where

    base
      : A₁ ⊔ A₂
      → B₁ ⊔ B₂
    base (ι₁ x₁)
      = ι₁ (Function.base F₁ x₁)
    base (ι₂ x₂)
      = ι₂ (Function.base F₂ x₂)

  function-sum
    : Function A₁ B₁
    → Function A₂ B₂
    → Function (A₁ ⊔ A₂) (B₁ ⊔ B₂)
  function-sum F₁ F₂
    = record {FunctionSum F₁ F₂}

