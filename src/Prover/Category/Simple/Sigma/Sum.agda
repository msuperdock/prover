module Prover.Category.Simple.Sigma.Sum where

open import Prover.Category.Simple
  using (PartialDependentFunction; PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

partial-function-sigma-sum
  : (A₁ B₁ : Set)
  → (A₂ B₂ : B₁ → Set)
  → PartialDependentFunction A₂ B₂
  → PartialFunction (A₁ ⊔ Σ B₁ A₂) (Σ B₁ B₂)
partial-function-sigma-sum _ _ _ _ _ (ι₁ _)
  = nothing
partial-function-sigma-sum _ _ _ _ f₂ (ι₂ (y₁ , x₂))
  with f₂ y₁ x₂
... | nothing
  = nothing
... | just y₂
  = just (y₁ , y₂)

