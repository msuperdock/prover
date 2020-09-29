module Prover.Function.Dependent.Sigma where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Prelude

-- ## Types

dependent-set-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : DependentCategory C)
  → DependentSet (chain-category-snoc C₁')
  → DependentSet C

-- ## Definitions

dependent-set-sigma {n = zero} C₁' C₂'
  = Σ (Category.Object C₁') (DependentSet.set C₂')

dependent-set-sigma {n = suc _} C₁' C₂'
  = record
  { set
    = λ x → dependent-set-sigma
      (DependentCategory.category C₁' x)
      (DependentSet.set C₂' x)
  }

