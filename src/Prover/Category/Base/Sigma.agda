module Prover.Category.Base.Sigma where

open import Prover.Category.Base
  using (Function)
open import Prover.Prelude

-- ## Function

function-sigma
  : {A₁ B₁ B₂ : Set}
  → (A₂ : A₁ → Set)
  → Function A₁ B₁
  → ((x₁ : A₁) → Function (A₂ x₁) B₂)
  → Function (Σ A₁ A₂) (B₁ × B₂)
function-sigma _ f₁ f₂ (x₁ , x₂)
  = f₁ x₁
  , f₂ x₁ x₂

