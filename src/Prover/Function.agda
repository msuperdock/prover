module Prover.Function where

open import Prover.Prelude

-- ## Function

record Function
  (A B : Set)
  : Set
  where

  constructor

    function

  field

    base
      : A
      → B

-- ## FunctionEqual

record FunctionEqual
  {A B₁ B₂ : Set}
  (F₁ : Function A B₁)
  (F₂ : Function A B₂)
  : Set
  where

  field

    base
      : (x : A)
      → Function.base F₁ x ≅ Function.base F₂ x

-- ## FunctionIdentity

record FunctionIdentity
  {A₁ A₂ : Set}
  (F : Function A₁ A₂)
  : Set
  where

  field

    base
      : (x₁ : A₁)
      → Function.base F x₁ ≅ x₁

-- ## FunctionCompose

record FunctionCompose
  {A B C₁ C₂ : Set}
  (F : Function B C₁)
  (G : Function A B)
  (H : Function A C₂)
  : Set
  where

  field

    base
      : (x : A)
      → Function.base H x ≅ Function.base F (Function.base G x)

-- ## FunctionSquare

record FunctionSquare
  {A₁ A₂ B₁ B₂ B₃ : Set}
  (F : Function A₁ A₂)
  (G : Function B₁ B₃)
  (H₁ : Function A₁ B₁)
  (H₂ : Function A₂ B₂)
  : Set
  where

  field

    base
      : (x₁ : A₁)
      → Function.base H₂ (Function.base F x₁)
        ≅ Function.base G (Function.base H₁ x₁)

