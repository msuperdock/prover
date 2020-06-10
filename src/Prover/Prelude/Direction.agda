module Prover.Prelude.Direction where

open import Prover.Prelude.Decidable
  using (Decidable; no; yes)
open import Prover.Prelude.Equality
  using (_≢_; refl)

-- ## Definition

module _Direction where

  data Direction
    : Set
    where
  
    up
      : Direction
  
    down
      : Direction
  
    left
      : Direction
  
    right
      : Direction

Direction
  : Set
Direction
  = _Direction.Direction

-- ## Module

module Direction where

  open _Direction.Direction public

  reverse
    : Direction
    → Direction
  reverse up
    = down
  reverse down
    = up
  reverse left
    = right
  reverse right
    = left
  
  _≟_dir
    : Decidable Direction
  
  up ≟ up dir
    = yes refl
  down ≟ down dir
    = yes refl
  left ≟ left dir
    = yes refl
  right ≟ right dir
    = yes refl
  
  up ≟ down dir
    = no (λ ())
  up ≟ left dir
    = no (λ ())
  up ≟ right dir
    = no (λ ())
  down ≟ up dir
    = no (λ ())
  down ≟ left dir
    = no (λ ())
  down ≟ right dir
    = no (λ ())
  left ≟ up dir
    = no (λ ())
  left ≟ down dir
    = no (λ ())
  left ≟ right dir
    = no (λ ())
  right ≟ up dir
    = no (λ ())
  right ≟ down dir
    = no (λ ())
  right ≟ left dir
    = no (λ ())
  
  reverse-≢
    : (d : Direction)
    → reverse d ≢ d
  reverse-≢ up ()

-- ## Exports

open Direction public
  using (_≟_dir)

