module Prover.Function.Split where

open import Prover.Function
  using (Function; FunctionSquare)
open import Prover.Function.Partial
  using (PartialFunction; PartialFunctionSquare)
open import Prover.Prelude

open Prover.Function using () renaming
  ( function
    to function'
  )

open Prover.Function.Partial using () renaming
  ( partial-function
    to partial-function'
  )

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
      : (x : B)
      → base (unbase x) ≡ just x

-- ### Conversion

retraction-split
  : {A B : Set}
  → Retraction A B
  → SplitFunction A B
retraction-split F
  = record
  { partial-function
    = partial-function' (just ∘ Retraction.to F)
  ; function
    = function' (Retraction.from F)
  ; base-unbase
    = sub just ∘ Retraction.to-from F
  }

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

