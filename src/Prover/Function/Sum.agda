module Prover.Function.Sum where

open import Prover.Function
  using (Function)
open import Prover.Prelude

-- ## Function

function-sum
  : {A₁ A₂ B₁ B₂ : Set}
  → Function A₁ B₁
  → Function A₂ B₂
  → Function (A₁ ⊔ A₂) (B₁ ⊔ B₂)
function-sum f₁ _ (ι₁ x₁)
  = ι₁ (f₁ x₁)
function-sum _ f₂ (ι₂ x₂)
  = ι₂ (f₂ x₂)

