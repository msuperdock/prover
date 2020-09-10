module Prover.Function.Split.Sum where

open import Prover.Function
  using (Function)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Partial.Sum
  using (partial-function-sum)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Function.Sum
  using (function-sum)
open import Prover.Prelude

-- ## SplitFunction

module _
  {A₁ A₂ B₁ B₂ : Set}
  where

  module SplitFunctionSum
    (F₁ : SplitFunction A₁ B₁)
    (F₂ : SplitFunction A₂ B₂)
    where

    partial-function
      : PartialFunction (A₁ ⊔ A₂) (B₁ ⊔ B₂)
    partial-function
      = partial-function-sum
        (SplitFunction.partial-function F₁)
        (SplitFunction.partial-function F₂)

    open PartialFunction partial-function

    function
      : Function (B₁ ⊔ B₂) (A₁ ⊔ A₂)
    function
      = function-sum
        (SplitFunction.function F₁)
        (SplitFunction.function F₂)

    open Function function using () renaming
      ( base
        to unbase
      )

    base-unbase
      : (x' : B₁ ⊔ B₂)
      → base (unbase x') ≡ just x'
    base-unbase (ι₁ x₁')
      with SplitFunction.base F₁ (SplitFunction.unbase F₁ x₁')
      | SplitFunction.base-unbase F₁ x₁'
    ... | _ | refl
      = refl
    base-unbase (ι₂ x₂')
      with SplitFunction.base F₂ (SplitFunction.unbase F₂ x₂')
      | SplitFunction.base-unbase F₂ x₂'
    ... | _ | refl
      = refl

  split-function-sum
    : SplitFunction A₁ B₁
    → SplitFunction A₂ B₂
    → SplitFunction (A₁ ⊔ A₂) (B₁ ⊔ B₂)
  split-function-sum F₁ F₂
    = record {SplitFunctionSum F₁ F₂}

