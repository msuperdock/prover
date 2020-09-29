module Prover.Function.Dependent where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Prelude

-- ## Types

DependentSet
  : {n : ℕ}
  → ChainCategory n
  → Set₁

record DependentSet'
  {n : ℕ}
  (C : ChainCategory (suc n))
  : Set₁

-- ## Definitions

DependentSet {n = zero} _
  = Set
DependentSet {n = suc _} C
  = DependentSet' C

record DependentSet' C where

  inductive

  no-eta-equality

  field

    set
      : (x : ChainCategory.Object C)
      → DependentSet
        (ChainCategory.category' C x)

module DependentSet
  = DependentSet'

