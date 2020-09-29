module Prover.Category.Dependent.Encoding.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding
  using (DependentEncoding)
open import Prover.Category.Dependent.List
  using (dependent-category-list)
open import Prover.Category.Encoding.List
  using (encoding-list)
open import Prover.Prelude

-- ## Types

dependent-encoding-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {A : Set}
  → DependentEncoding C' A
  → DependentEncoding
    (dependent-category-list C')
    (List A)

-- ## Definitions

dependent-encoding-list {n = zero} e
  = encoding-list e

dependent-encoding-list {n = suc _} e
  = record
  { encoding
    = λ x → dependent-encoding-list
      (DependentEncoding.encoding e x)
  }

