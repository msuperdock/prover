module Prover.Category.Split.Base.Sigma.Sum where

open import Prover.Category.Split.Base
  using (SplitFunction)
open import Prover.Category.Split.Base.Sigma
  using (split-function-sigma)
open import Prover.Category.Split.Base.Sum
  using (split-function-sum)
open import Prover.Prelude

-- ## SplitFunction

split-function-sigma-sum
  : {A₁₁ A₂₁ A₂₂ B₁₁ B₂₁ : Set}
  → (B₂₂ : B₂₁ → Set)
  → SplitFunction A₁₁ B₁₁
  → SplitFunction A₂₁ B₂₁
  → ((y₂₁ : B₂₁) → SplitFunction A₂₂ (B₂₂ y₂₁))
  → SplitFunction (A₁₁ ⊔ A₂₁ × A₂₂) (B₁₁ ⊔ Σ B₂₁ B₂₂)
split-function-sigma-sum B₂₂ F₁₁ F₂₁ F₂₂
  = split-function-sum F₁₁
    (split-function-sigma B₂₂ F₂₁ F₂₂)

