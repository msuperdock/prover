module Prover.Function.Partial where

open import Prover.Function
  using (Function)
open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Prelude

-- ## PartialFunction

record PartialFunction
  (A B : Set)
  : Set
  where

  constructor

    partial-function

  field

    base
      : A
      → Maybe B

  bool-function
    : BoolFunction A
  bool-function x
    = Maybe.is-just (base x)

-- ## PartialFunctionSquare

record PartialFunctionSquare
  {A₁ A₂ B₁ B₂ : Set}
  (F : Function A₁ A₂)
  (G : Function B₁ B₂)
  (H₁ : PartialFunction A₁ B₁)
  (H₂ : PartialFunction A₂ B₂)
  : Set
  where

  field
  
    base
      : {x₁' : B₁}
      → (x₁ : A₁)
      → PartialFunction.base H₁ x₁ ≡ just x₁'
      → PartialFunction.base H₂ (Function.base F x₁)
        ≡ just (Function.base G x₁')

