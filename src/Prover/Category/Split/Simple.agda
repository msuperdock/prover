module Prover.Category.Split.Simple where

open import Prover.Category
  using (Category)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Prelude

-- ## SplitFunction

-- ### Definition

record SplitFunction
  (A B : Set)
  : Set
  where

  field

    partial-function
      : A
      → Maybe B

    function
      : B
      → A

    valid
      : (y : B)
      → partial-function (function y) ≡ just y

-- ### Conversion

-- #### Retraction

module _
  {A B : Set}
  where

  module SplitFunctionFromRetraction
    (F : Retraction A B)
    where

    partial-function
      : A
      → Maybe B
    partial-function x
      = just (Retraction.to F x)

    function
      : B
      → A
    function
      = Retraction.from F

    valid
      : (y : B)
      → partial-function (function y) ≡ just y
    valid y
      = sub just (Retraction.to-from F y)

  split-function-from-retraction
    : Retraction A B
    → SplitFunction A B
  split-function-from-retraction F
    = record {SplitFunctionFromRetraction F}

-- #### SplitFunctor

module _
  {C D : Category}
  where

  module SplitFunctorSimple
    (F : SplitFunctor C D)
    where

    partial-function
      : Category.Object C
      → Maybe (Category.Object D)
    partial-function
      = SplitFunctor.base F

    function
      : Category.Object D
      → Category.Object C
    function
      = SplitFunctor.unbase F

    valid
      : (y : Category.Object D)
      → partial-function (function y) ≡ just y
    valid
      = SplitFunctor.base-unbase F

  split-functor-simple
    : SplitFunctor C D
    → SplitFunction
      (Category.Object C)
      (Category.Object D)
  split-functor-simple F
    = record {SplitFunctorSimple F}

