module Prover.Function.Bool.Sigma.Sum where

open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Prelude

-- ## BoolFunction

bool-function-sigma-sum
  : {A₁₁ A₂₁ : Set}
  → (A₂₂ : A₂₁ → Set)
  → ((x₂₁ : A₂₁) → BoolFunction (A₂₂ x₂₁))
  → BoolFunction (A₁₁ ⊔ Σ A₂₁ A₂₂)
bool-function-sigma-sum _ _ (ι₁ _)
  = false
bool-function-sigma-sum _ f₂₂ (ι₂ (x₂₁ , x₂₂))
  = f₂₂ x₂₁ x₂₂

