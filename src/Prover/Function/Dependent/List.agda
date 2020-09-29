module Prover.Function.Dependent.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Prelude

-- ## Types

dependent-set-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → DependentSet C

-- ## Definitions

dependent-set-list {n = zero} C'
  = List C'

dependent-set-list {n = suc _} C'
  = record
  { set
    = λ x → dependent-set-list
      (DependentSet.set C' x)
  }

