module Prover.Function.Partial.Sigma.Sum where

open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

partial-function-sigma-sum
  : {A₁₁ A₂₁ : Set}
  → (A₂₂ B₂₂ : A₂₁ → Set)
  → ((x₂₁ : A₂₁) → PartialFunction (A₂₂ x₂₁) (B₂₂ x₂₁))
  → PartialFunction (A₁₁ ⊔ Σ A₂₁ A₂₂) (Σ A₂₁ B₂₂)
partial-function-sigma-sum _ _ _ (ι₁ _)
  = nothing
partial-function-sigma-sum _ _ f₂₂ (ι₂ (x₂₁ , x₂₂))
  with f₂₂ x₂₁ x₂₂
... | nothing
  = nothing
... | just y₂₂
  = just (x₂₁ , y₂₂)

