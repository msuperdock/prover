module Prover.Function.Partial.Sum where

open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

partial-function-sum
  : {A₁ A₂ B₁ B₂ : Set}
  → PartialFunction A₁ B₁
  → PartialFunction A₂ B₂
  → PartialFunction (A₁ ⊔ A₂) (B₁ ⊔ B₂)
partial-function-sum f₁ _ (ι₁ x₁)
  = Maybe.map ι₁ (f₁ x₁)
partial-function-sum _ f₂ (ι₂ x₂)
  = Maybe.map ι₂ (f₂ x₂)

