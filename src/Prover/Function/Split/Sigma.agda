module Prover.Function.Split.Sigma where

open import Prover.Function
  using (Function)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Partial.Sigma
  using (partial-function-sigma)
open import Prover.Function.Sigma
  using (function-sigma)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Prelude

-- ## SplitFunction

module _
  {A₁ A₂ B₁ : Set}
  where

  module SplitFunctionSigma
    (B₂ : B₁ → Set)
    (F₁ : SplitFunction A₁ B₁)
    (F₂ : (x₁' : B₁) → SplitFunction A₂ (B₂ x₁'))
    where

    partial-function
      : PartialFunction (A₁ × A₂) (Σ B₁ B₂)
    partial-function
      = partial-function-sigma B₂
        (SplitFunction.partial-function F₁)
        (λ y₁ → SplitFunction.partial-function (F₂ y₁))

    open PartialFunction partial-function

    function
      : Function (Σ B₁ B₂) (A₁ × A₂)
    function
      = function-sigma B₂
        (SplitFunction.function F₁)
        (λ y₁ → SplitFunction.function (F₂ y₁))

    open Function function using () renaming
      ( base
        to unbase
      )

    base-unbase
      : (x' : Σ B₁ B₂)
      → base (unbase x') ≡ just x'
    base-unbase (x₁' , x₂')
      with SplitFunction.base F₁ (SplitFunction.unbase F₁ x₁')
      | SplitFunction.base-unbase F₁ x₁'
    ... | _ | refl
      with SplitFunction.base (F₂ x₁') (SplitFunction.unbase (F₂ x₁') x₂')
      | SplitFunction.base-unbase (F₂ x₁') x₂'
    ... | _ | refl
      = refl

  split-function-sigma
    : (B₂ : B₁ → Set)
    → SplitFunction A₁ B₁
    → ((x₁' : B₁) → SplitFunction A₂ (B₂ x₁'))
    → SplitFunction (A₁ × A₂) (Σ B₁ B₂)
  split-function-sigma B₂ F₁ F₂
    = record {SplitFunctionSigma B₂ F₁ F₂}

