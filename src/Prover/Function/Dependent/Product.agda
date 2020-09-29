module Prover.Function.Dependent.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Prelude

-- ## Types

dependent-set-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → DependentSet C
  → DependentSet C

-- ## Definitions

dependent-set-product {n = zero} C₁' C₂'
  = C₁' × C₂'

dependent-set-product {n = suc _} C₁' C₂'
  = record
  { set
    = λ x → dependent-set-product
      (DependentSet.set C₁' x)
      (DependentSet.set C₂' x)
  }

