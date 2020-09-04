module Prover.Function.Dependent.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet; cons; dependent-set₀; nil)
open import Prover.Prelude

-- ## DependentSet

dependent-set-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → DependentSet C
dependent-set-list
  {n = zero} C'
  = nil
    (List
      (dependent-set₀ C'))
dependent-set-list
  {n = suc _} C'
  = cons
    (λ x → dependent-set-list
      (DependentSet.tail C' x))

