module Prover.Function.Dependent.Sigma where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory; dependent-category₀)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Dependent
  using (DependentSet; cons; dependent-set₀; nil)
open import Prover.Prelude

-- ## DependentSet

dependent-set-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : DependentCategory C)
  → DependentSet (chain-category-snoc C₁')
  → DependentSet C
dependent-set-sigma
  {n = zero} C₁' C₂'
  = nil
    (Σ
      (Category.Object
        (dependent-category₀ C₁'))
      (λ x → dependent-set₀
        (DependentSet.tail C₂' x)))
dependent-set-sigma
  {n = suc _} C₁' C₂'
  = cons
    (λ x → dependent-set-sigma
      (DependentCategory.tail C₁' x)
      (DependentSet.tail C₂' x))

