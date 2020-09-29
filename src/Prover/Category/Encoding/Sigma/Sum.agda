module Prover.Category.Encoding.Sigma.Sum where

open import Prover.Category.Encoding
  using (Encoding)
open import Prover.Category.Encoding.Sigma
  using (encoding-sigma)
open import Prover.Category.Encoding.Sum
  using (encoding-sum)
open import Prover.Prelude

-- ## Encoding

encoding-sigma-sum
  : {A₁₁ A₂₁ B₁₁ B₂₁ B₂₂ : Set}
  → (A₂₂ : A₂₁ → Set)
  → Encoding A₁₁ B₁₁
  → Encoding A₂₁ B₂₁
  → ((x₂₁ : A₂₁) → Encoding (A₂₂ x₂₁) B₂₂)
  → Encoding (A₁₁ ⊔ Σ A₂₁ A₂₂) (B₁₁ ⊔ B₂₁ × B₂₂)
encoding-sigma-sum A₂₂ e₁₁ e₂₁ e₂₂
  = encoding-sum e₁₁
    (encoding-sigma A₂₂ e₂₁ e₂₂)

