module Prover.Function.Dependent.Simple.Bool where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; dependent-simple-category₀)
open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definition

  data DependentSimpleBoolFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → DependentSimpleCategory C
    → Set
    where

    nil
      : {C : ChainCategory zero}
      → {C' : DependentSimpleCategory C}
      → BoolFunction (dependent-simple-category₀ C')
      → DependentSimpleBoolFunction C'

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : DependentSimpleCategory C}
      → ((x : Category.Object (ChainCategory.head C))
        → DependentSimpleBoolFunction (DependentSimpleCategory.tail C' x))
      → DependentSimpleBoolFunction C'

  -- ### Interface

  dependent-simple-bool-function₀
    : {C : ChainCategory zero}
    → {C' : DependentSimpleCategory C}
    → DependentSimpleBoolFunction C'
    → BoolFunction (dependent-simple-category₀ C')
  dependent-simple-bool-function₀ (nil f)
    = f

  dependent-simple-bool-function-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → DependentSimpleBoolFunction C'
    → (x : Category.Object (ChainCategory.head C))
    → DependentSimpleBoolFunction
      (DependentSimpleCategory.tail C' x)
  dependent-simple-bool-function-tail (cons F)
    = F

-- ## Modules

DependentSimpleBoolFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → Set
DependentSimpleBoolFunction
  = Internal.DependentSimpleBoolFunction

open Internal.DependentSimpleBoolFunction public

open Internal public
  using (dependent-simple-bool-function₀)

module DependentSimpleBoolFunction where

  open Internal public using () renaming
    ( dependent-simple-bool-function-tail
      to tail
    )

