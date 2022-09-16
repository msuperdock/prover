module Prover.Data.Sigma where

import Data.Sigma
  as Sigma'

-- ## Module

open Sigma' public
  using (Σ; _×_; _,_; π₁; π₂)

module Sigma where

  map
    : {A₁ : Set}
    → {A₂ B₂ : A₁ → Set}
    → ((x₁ : A₁) → A₂ x₁ → B₂ x₁)
    → Σ A₁ A₂
    → Σ A₁ B₂
  map f (x₁ , x₂)
    = (x₁ , f x₁ x₂)

