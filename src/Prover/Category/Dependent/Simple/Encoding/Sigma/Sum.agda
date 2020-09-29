module Prover.Category.Dependent.Simple.Encoding.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding
  using (DependentEncoding)
open import Prover.Category.Dependent.Encoding.Sigma.Sum
  using (dependent-encoding-sigma-sum)
open import Prover.Category.Dependent.Encoding.Unit
  using (dependent-encoding-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Encoding
  using (DependentSimpleEncoding)
open import Prover.Category.Dependent.Simple.Encoding.Convert
  using (dependent-encoding-simple)
open import Prover.Category.Dependent.Simple.Sigma.Sum
  using (dependent-simple-category-sigma-sum)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## DependentSimpleEncoding

dependent-simple-encoding-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {C₂₂' : DependentSimpleCategory (chain-category-snoc C₂₁')}
  → (F₁ : DependentSplitFunctor C₁₁' C₂₁')
  → {A₁₁ A₂₁ A₂₂ : Set}
  → DependentEncoding C₁₁' A₁₁
  → DependentEncoding C₂₁' A₂₁
  → DependentSimpleEncoding C₂₂' A₂₂
  → DependentSimpleEncoding
    (dependent-simple-category-sigma-sum C₂₂' F₁)
    (A₁₁ ⊔ A₂₁ × A₂₂)
dependent-simple-encoding-sigma-sum F₁ e₁₁ e₂₁ e₂₂
  = dependent-encoding-simple
  $ dependent-encoding-sigma-sum F₁ e₁₁ e₂₁
    (dependent-encoding-unit e₂₂)

