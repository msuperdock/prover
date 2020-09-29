module Prover.Category.Dependent.Simple.Encoding.Convert where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding
  using (DependentEncoding)
open import Prover.Category.Dependent.Simple.Convert
  using (dependent-category-simple)
open import Prover.Category.Dependent.Simple.Encoding
  using (DependentSimpleEncoding)
open import Prover.Prelude

-- ## Types

dependent-encoding-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {A : Set}
  → DependentEncoding C' A
  → DependentSimpleEncoding
    (dependent-category-simple C') A

-- ## Definitions

dependent-encoding-simple {n = zero} e
  = e

dependent-encoding-simple {n = suc _} e
  = record
  { encoding
    = λ x → dependent-encoding-simple
      (DependentEncoding.encoding e x)
  }

