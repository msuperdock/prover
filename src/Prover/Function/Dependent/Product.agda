module Prover.Function.Dependent.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet; cons; dependent-set₀; nil)
open import Prover.Prelude

-- ## DependentSet

dependent-set-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → DependentSet C
  → DependentSet C
dependent-set-product
  {n = zero} C₁' C₂'
  = nil
    (_×_
      (dependent-set₀ C₁')
      (dependent-set₀ C₂'))
dependent-set-product
  {n = suc _} C₁' C₂'
  = cons
    (λ x → dependent-set-product
      (DependentSet.tail C₁' x)
      (DependentSet.tail C₂' x))

