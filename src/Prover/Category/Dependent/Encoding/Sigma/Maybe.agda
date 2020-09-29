module Prover.Category.Dependent.Encoding.Sigma.Maybe where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding
  using (DependentEncoding)
open import Prover.Category.Dependent.Sigma.Maybe
  using (dependent-category-sigma-maybe)
open import Prover.Category.Dependent1
  using (Dependent₁Category)
open import Prover.Category.Encoding.Sigma
  using (encoding-sigma)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## Types

dependent-encoding-sigma-maybe
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → {A₁ A₂ : Set}
  → DependentEncoding C₁' A₁
  → DependentEncoding C₂' A₂
  → DependentEncoding
    (dependent-category-sigma-maybe C₁' C₂')
    (A₁ × A₂)

-- ## Definitions

dependent-encoding-sigma-maybe {n = zero} {C₂' = C₂'} e₁ e₂
  = encoding-sigma
    (Dependent₁Category.Object C₂') e₁
    (DependentEncoding.encoding e₂)

dependent-encoding-sigma-maybe {n = suc _} e₁ e₂
  = record
  { encoding
    = λ x → dependent-encoding-sigma-maybe
      (DependentEncoding.encoding e₁ x)
      (DependentEncoding.encoding e₂ x)
  }

