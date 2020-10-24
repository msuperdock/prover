module Prover.Category.Dependent1.Partial where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)

-- ## Dependent₁PartialFunctor

record Dependent₁PartialFunctor
  {C : Category}
  (C' D' : Dependent₁Category C)
  : Set
  where

  no-eta-equality

  field

    partial-functor
      : (x : Category.Object C)
      → PartialFunctor
        (Dependent₁Category.category C' x)
        (Dependent₁Category.category D' x)

  open module PartialFunctor' x
    = PartialFunctor (partial-functor x)
    public

  field

    partial-functor-square
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → PartialFunctorSquare
        (Dependent₁Category.functor C' f)
        (Dependent₁Category.functor D' f)
        (partial-functor x)
        (partial-functor y)

  open module PartialFunctorSquare' {x} {y} f
    = PartialFunctorSquare (partial-functor-square {x = x} {y = y} f)
    public using () renaming
    ( base
      to base-square
    ; map''
      to map-square''
    )

-- ## Dependent₁PartialFunctorSquare

record Dependent₁PartialFunctorSquare
  {C₁ C₂ : Category}
  {C₁' D₁' : Dependent₁Category C₁}
  {C₂' D₂' : Dependent₁Category C₂}
  {F : Functor C₁ C₂}
  (F' : Dependent₁Functor C₁' C₂' F)
  (G' : Dependent₁Functor D₁' D₂' F)
  (H₁ : Dependent₁PartialFunctor C₁' D₁')
  (H₂ : Dependent₁PartialFunctor C₂' D₂')
  : Set
  where

  field

    partial-functor
      : (x₁ : Category.Object C₁)
      → PartialFunctorSquare
        (Dependent₁Functor.functor F' x₁)
        (Dependent₁Functor.functor G' x₁)
        (Dependent₁PartialFunctor.partial-functor H₁ x₁)
        (Dependent₁PartialFunctor.partial-functor H₂ (Functor.base F x₁))

  open module PartialFunctor' x₁
    = PartialFunctorSquare (partial-functor x₁)
    public

