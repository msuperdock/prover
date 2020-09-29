module Prover.Category.Dependent.Simple.Bool where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Function
  using (DependentSimpleFunction)
open import Prover.Prelude

-- ## DependentSimpleBoolFunction

DependentSimpleBoolFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → Set
DependentSimpleBoolFunction C'
  = DependentSimpleFunction C' Bool

module DependentSimpleBoolFunction
  = DependentSimpleFunction
  using () renaming
  ( function
    to bool-function
  )

