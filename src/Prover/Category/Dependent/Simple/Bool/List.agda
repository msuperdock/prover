module Prover.Category.Dependent.Simple.Bool.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Category.Dependent.Simple.List
  using (dependent-simple-category-list)
open import Prover.Function.Bool.List
  using (bool-function-list)
open import Prover.Prelude

-- ## Types

dependent-simple-bool-function-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleBoolFunction C'
  → DependentSimpleBoolFunction
    (dependent-simple-category-list C')

-- ## Definitions

dependent-simple-bool-function-list {n = zero} F
  = bool-function-list F

dependent-simple-bool-function-list {n = suc _} F
  = record
  { function
    = λ x → dependent-simple-bool-function-list
      (DependentSimpleBoolFunction.bool-function F x)
  }

