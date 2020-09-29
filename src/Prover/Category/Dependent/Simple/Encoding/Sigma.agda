module Prover.Category.Dependent.Simple.Encoding.Sigma where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding
  using (DependentEncoding)
open import Prover.Category.Dependent.Encoding.Sigma.Maybe
  using (dependent-encoding-sigma-maybe)
open import Prover.Category.Dependent.Encoding.Unit
  using (dependent-encoding-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Encoding
  using (DependentSimpleEncoding)
open import Prover.Category.Dependent.Simple.Encoding.Convert
  using (dependent-encoding-simple)
open import Prover.Category.Dependent.Simple.Sigma
  using (dependent-simple-category-sigma)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## DependentSimpleEncoding

dependent-simple-encoding-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentSimpleCategory (chain-category-snoc C₁')}
  → {A₁ A₂ : Set}
  → DependentEncoding C₁' A₁
  → DependentSimpleEncoding C₂' A₂
  → DependentSimpleEncoding
    (dependent-simple-category-sigma C₁' C₂')
    (A₁ × A₂)
dependent-simple-encoding-sigma e₁ e₂
  = dependent-encoding-simple
  $ dependent-encoding-sigma-maybe e₁
    (dependent-encoding-unit e₂)

