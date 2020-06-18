module Prover.Category.Split.Base.Sigma where

open import Prover.Category.Base
  using (Function)
open import Prover.Category.Base.Sigma
  using (function-sigma)
open import Prover.Category.Partial.Base
  using (PartialFunction)
open import Prover.Category.Partial.Base.Sigma
  using (partial-function-sigma)
open import Prover.Category.Split.Base
  using (SplitFunction)
open import Prover.Prelude

-- ## SplitFunction

module _
  {A₁ A₂ B₁ : Set}
  where

  module SplitFunctionSigma
    (B₂ : B₁ → Set)
    (F₁ : SplitFunction A₁ B₁)
    (F₂ : (y₁ : B₁) → SplitFunction A₂ (B₂ y₁))
    where

    partial-function
      : PartialFunction (A₁ × A₂) (Σ B₁ B₂)
    partial-function
      = partial-function-sigma B₂
        (SplitFunction.partial-function F₁)
        (λ y₁ → SplitFunction.partial-function (F₂ y₁))

    function
      : Function (Σ B₁ B₂) (A₁ × A₂)
    function
      = function-sigma B₂
        (SplitFunction.function F₁)
        (λ y₁ → SplitFunction.function (F₂ y₁))

    valid
      : (y : Σ B₁ B₂)
      → partial-function (function y) ≡ just y
    valid (y₁ , y₂)
      with SplitFunction.partial-function F₁
        (SplitFunction.function F₁ y₁)
      | SplitFunction.valid F₁ y₁
    ... | _ | refl
      with SplitFunction.partial-function (F₂ y₁)
        (SplitFunction.function (F₂ y₁) y₂)
      | SplitFunction.valid (F₂ y₁) y₂
    ... | _ | refl
      = refl

  split-function-sigma
    : (B₂ : B₁ → Set)
    → SplitFunction A₁ B₁
    → ((y₁ : B₁) → SplitFunction A₂ (B₂ y₁))
    → SplitFunction (A₁ × A₂) (Σ B₁ B₂)
  split-function-sigma B₂ F₁ F₂
    = record {SplitFunctionSigma B₂ F₁ F₂}

