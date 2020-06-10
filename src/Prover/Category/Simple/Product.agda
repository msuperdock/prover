module Prover.Category.Simple.Product where

open import Prover.Category.Simple
  using (Function; PartialFunction; PartialRetraction)
open import Prover.Prelude

-- ## Function

function-product
  : {A₁ A₂ B₁ B₂ : Set}
  → Function A₁ B₁
  → Function A₂ B₂
  → Function (A₁ × A₂) (B₁ × B₂)
function-product f₁ f₂ (x₁ , x₂)
  = (f₁ x₁ , f₂ x₂)

-- ## PartialFunction

partial-function-product
  : {A₁ A₂ B₁ B₂ : Set}
  → PartialFunction A₁ B₁
  → PartialFunction A₂ B₂
  → PartialFunction (A₁ × A₂) (B₁ × B₂)
partial-function-product f₁ f₂ (x₁ , x₂)
  with f₁ x₁ | f₂ x₂
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just y₁ | just y₂
  = just (y₁ , y₂)

-- ## PartialRetraction

module _
  {A₁ A₂ B₁ B₂ : Set}
  where

  module PartialRetractionProduct
    (F₁ : PartialRetraction A₁ B₁)
    (F₂ : PartialRetraction A₂ B₂)
    where

    to
      : A₁ × A₂
      → Maybe (B₁ × B₂)
    to
      = partial-function-product
        (PartialRetraction.to F₁)
        (PartialRetraction.to F₂)

    from
      : B₁ × B₂
      → A₁ × A₂
    from
      = function-product
        (PartialRetraction.from F₁)
        (PartialRetraction.from F₂)

    to-from
      : (y : B₁ × B₂)
      → to (from y) ≡ just y
    to-from (y₁ , y₂)
      with PartialRetraction.to F₁ (PartialRetraction.from F₁ y₁)
      | PartialRetraction.to-from F₁ y₁
      | PartialRetraction.to F₂ (PartialRetraction.from F₂ y₂)
      | PartialRetraction.to-from F₂ y₂
    ... | _ | refl | _ | refl
      = refl
  
  partial-retraction-product
    : PartialRetraction A₁ B₁
    → PartialRetraction A₂ B₂
    → PartialRetraction (A₁ × A₂) (B₁ × B₂)
  partial-retraction-product F₁ F₂
    = record {PartialRetractionProduct F₁ F₂}

