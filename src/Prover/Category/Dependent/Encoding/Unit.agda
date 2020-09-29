module Prover.Category.Dependent.Encoding.Unit where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Encoding
  using (DependentEncoding)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Encoding
  using (DependentSimpleEncoding)
open import Prover.Category.Dependent.Unit
  using (dependent-category-unit)
open import Prover.Prelude

-- ## Types

dependent-encoding-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {A : Set}
  → DependentSimpleEncoding C' A
  → DependentEncoding
    (dependent-category-unit C') A

-- ## Definitions

dependent-encoding-unit {n = zero} e
  = e

dependent-encoding-unit {n = suc _} e
  = record
  { encoding
    = λ x → dependent-encoding-unit
      (DependentSimpleEncoding.encoding e x)
  }

