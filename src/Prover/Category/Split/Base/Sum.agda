module Prover.Category.Split.Base.Sum where

open import Prover.Category.Base
  using (Function)
open import Prover.Category.Base.Sum
  using (function-sum)
open import Prover.Category.Partial.Base
  using (PartialFunction)
open import Prover.Category.Partial.Base.Sum
  using (partial-function-sum)
open import Prover.Category.Split.Base
  using (SplitFunction)
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

    function
      : Function (B₁ ⊔ B₂) (A₁ ⊔ A₂)
    function
      = function-sum
        (SplitFunction.function F₁)
        (SplitFunction.function F₂)

    valid
      : (y : B₁ ⊔ B₂)
      → partial-function (function y) ≡ just y
    valid (ι₁ y₁)
      with SplitFunction.partial-function F₁ (SplitFunction.function F₁ y₁)
      | SplitFunction.valid F₁ y₁
    ... | _ | refl
      = refl
    valid (ι₂ y₂)
      with SplitFunction.partial-function F₂ (SplitFunction.function F₂ y₂)
      | SplitFunction.valid F₂ y₂
    ... | _ | refl
      = refl

  split-function-sum
    : SplitFunction A₁ B₁
    → SplitFunction A₂ B₂
    → SplitFunction (A₁ ⊔ A₂) (B₁ ⊔ B₂)
  split-function-sum F₁ F₂
    = record {SplitFunctionSum F₁ F₂}

