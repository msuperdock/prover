module Prover.Function.Sigma where

open import Prover.Function
  using (Function)
open import Prover.Prelude

-- ## Function

module _
  {A₁ B₁ B₂ : Set}
  where

  module FunctionSigma
    (A₂ : A₁ → Set)
    (F₁ : Function A₁ B₁)
    (F₂ : (x₁ : A₁) → Function (A₂ x₁) B₂)
    where

    base
      : Σ A₁ A₂
      → B₁ × B₂
    base (x₁ , x₂)
      = Function.base F₁ x₁
      , Function.base (F₂ x₁) x₂

  function-sigma
    : (A₂ : A₁ → Set)
    → Function A₁ B₁
    → ((x₁ : A₁) → Function (A₂ x₁) B₂)
    → Function (Σ A₁ A₂) (B₁ × B₂)
  function-sigma A₂ F₁ F₂
    = record {FunctionSigma A₂ F₁ F₂}

