module Prover.Function.Partial.Sigma where

open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

module _
  {A₁ A₂ B₁ : Set}
  where

  module PartialFunctionSigma
    (B₂ : B₁ → Set)
    (F₁ : PartialFunction A₁ B₁)
    (F₂ : (y₁ : B₁) → PartialFunction A₂ (B₂ y₁))
    where

    base
      : A₁ × A₂
      → Maybe (Σ B₁ B₂)
    base (x₁ , x₂)
      with PartialFunction.base F₁ x₁
    ... | nothing
      = nothing
    ... | just x₁'
      with PartialFunction.base (F₂ x₁') x₂
    ... | nothing
      = nothing
    ... | just x₂'
      = just (x₁' , x₂')

  partial-function-sigma
    : (B₂ : B₁ → Set)
    → PartialFunction A₁ B₁
    → ((y₁ : B₁) → PartialFunction A₂ (B₂ y₁))
    → PartialFunction (A₁ × A₂) (Σ B₁ B₂)
  partial-function-sigma B₂ F₁ F₂
   = record {PartialFunctionSigma B₂ F₁ F₂}

