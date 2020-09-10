module Prover.Function.Partial.Sigma.Sum where

open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

module _
  {A₁₁ A₂₁ : Set}
  where

  module PartialFunctionSigmaSum
    (A₂₂ B₂₂ : A₂₁ → Set)
    (F₂₂ : (x₂₁ : A₂₁) → PartialFunction (A₂₂ x₂₁) (B₂₂ x₂₁))
    where

    base
      : A₁₁ ⊔ Σ A₂₁ A₂₂
      → Maybe (Σ A₂₁ B₂₂)
    base (ι₁ _)
      = nothing
    base (ι₂ (x₂₁ , x₂₂))
      with PartialFunction.base (F₂₂ x₂₁) x₂₂
    ... | nothing
      = nothing
    ... | just y₂₂
      = just (x₂₁ , y₂₂)

  partial-function-sigma-sum
    : (A₂₂ B₂₂ : A₂₁ → Set)
    → ((x₂₁ : A₂₁) → PartialFunction (A₂₂ x₂₁) (B₂₂ x₂₁))
    → PartialFunction (A₁₁ ⊔ Σ A₂₁ A₂₂) (Σ A₂₁ B₂₂)
  partial-function-sigma-sum A₂₂ B₂₂ F₂₂
    = record {PartialFunctionSigmaSum A₂₂ B₂₂ F₂₂}

