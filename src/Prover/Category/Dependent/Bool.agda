module Prover.Category.Dependent.Bool where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Function
  using (DependentFunction)
open import Prover.Prelude

-- ## DependentBoolFunction

DependentBoolFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → Set
DependentBoolFunction C'
  = DependentFunction C' Bool

