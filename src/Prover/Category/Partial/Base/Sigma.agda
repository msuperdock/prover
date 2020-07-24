module Prover.Category.Partial.Base.Sigma where

open import Prover.Category.Partial.Base
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

partial-function-sigma
  : {A₁ A₂ B₁ : Set}
  → (B₂ : B₁ → Set)
  → PartialFunction A₁ B₁
  → ((y₁ : B₁) → PartialFunction A₂ (B₂ y₁))
  → PartialFunction (A₁ × A₂) (Σ B₁ B₂)
partial-function-sigma _ f₁ f₂ (x₁ , x₂)
  with f₁ x₁
... | nothing
  = nothing
... | just x₁'
  with f₂ x₁' x₂
... | nothing
  = nothing
... | just x₂'
  = just (x₁' , x₂')

