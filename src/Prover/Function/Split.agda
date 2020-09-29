module Prover.Function.Split where

open import Prover.Function
  using (Function; FunctionSquare)
open import Prover.Function.Partial
  using (PartialFunction; PartialFunctionSquare)
open import Prover.Prelude

-- ## SplitFunction

-- ### Definition

record SplitFunction
  (A B : Set)
  : Set
  where

  field

    partial-function
      : PartialFunction A B

  open PartialFunction partial-function public

  field

    function
      : Function B A

  open Function function public using () renaming
    ( base
      to unbase
    )

  field

    base-unbase
      : (x' : B)
      → base (unbase x') ≡ just x'

-- ### Conversion

module _
  {A B : Set}
  where

  module SplitFunctionFromRetraction
    (F : Retraction A B)
    where

    open Retraction F public using () renaming
      ( from
        to unbase
      )

    base
      : A
      → Maybe B
    base x
      = just (Retraction.to F x)

    partial-function
      : PartialFunction A B
    partial-function
      = record
      { base
        = base
      }

    function
      : Function B A
    function
      = record
      { base
        = unbase
      }

    base-unbase
      : (x' : B)
      → base (unbase x') ≡ just x'
    base-unbase x'
      = sub just (Retraction.to-from F x')

  split-function-from-retraction
    : Retraction A B
    → SplitFunction A B
  split-function-from-retraction F
    = record {SplitFunctionFromRetraction F}

-- ## SplitFunctionSquare

record SplitFunctionSquare
  {A₁ A₂ B₁ B₂ : Set}
  (F : Function A₁ A₂)
  (G : Function B₁ B₂)
  (H₁ : SplitFunction A₁ B₁)
  (H₂ : SplitFunction A₂ B₂)
  : Set
  where

  field

    partial-function
      : PartialFunctionSquare F G
        (SplitFunction.partial-function H₁)
        (SplitFunction.partial-function H₂)

    function
      : FunctionSquare G F
        (SplitFunction.function H₁)
        (SplitFunction.function H₂)

