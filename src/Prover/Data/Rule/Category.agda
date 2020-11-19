module Prover.Data.Rule.Category where

open import Prover.Category
  using (Precategory)
open import Prover.Category.List.Unit
  using (module CategoryListUnit)
open import Prover.Data.Rule
  using (Rule; rule)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Variables.Category
  using (module CategoryVariables)

-- ## Precategory

module PrecategoryRule
  (ss : Symbols)
  where

  Object
    : Set
  Object
    = Rule ss

  record Arrow
    (r s : Object)
    : Set
    where

    constructor

      arrow

    field

      variables
        : CategoryVariables.Arrow
          (Rule.variables r)
          (Rule.variables s)

      hypotheses
        : CategoryListUnit.Arrow
          (Rule.hypotheses r)
          (Rule.hypotheses s)

  record ArrowEqual
    {r s : Object}
    (f₁ f₂ : Arrow r s)
    : Set
    where

    constructor

      arrow-equal

    field

      variables
        : CategoryVariables.ArrowEqual
          (Arrow.variables f₁)
          (Arrow.variables f₂)

      hypotheses
        : CategoryListUnit.ArrowEqual
          (Arrow.hypotheses f₁)
          (Arrow.hypotheses f₂)

  abstract

    arrow-refl
      : {x y : Object}
      → {f : Arrow x y}
      → ArrowEqual f f
    arrow-refl
      = record
      { variables
        = CategoryVariables.arrow-refl
      ; hypotheses
        = CategoryListUnit.arrow-refl
      }

    arrow-sym
      : {x y : Object}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁
    arrow-sym (arrow-equal ps qs)
      = record
      { variables
        = CategoryVariables.arrow-sym ps
      ; hypotheses
        = CategoryListUnit.arrow-sym qs
      }

    arrow-trans
      : {x y : Object}
      → {f₁ f₂ f₃ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃
    arrow-trans (arrow-equal ps₁ qs₁) (arrow-equal ps₂ qs₂)
      = record
      { variables
        = CategoryVariables.arrow-trans ps₁ ps₂
      ; hypotheses
        = CategoryListUnit.arrow-trans qs₁ qs₂
      }

  identity
    : (x : Object)
    → Arrow x x
  identity (rule _ vs hs _)
    = record
    { variables
      = CategoryVariables.identity vs
    ; hypotheses
      = CategoryListUnit.identity hs
    }

  compose
    : {x y z : Object}
    → Arrow y z
    → Arrow x y
    → Arrow x z
  compose (arrow fs gs) (arrow hs is)
    = record
    { variables
      = CategoryVariables.compose fs hs
    ; hypotheses
      = CategoryListUnit.compose gs is
    }

precategory-rule
  : Symbols
  → Precategory
precategory-rule ss
  = record {PrecategoryRule ss}

