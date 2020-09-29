module Prover.Category.Dependent.Encoding.Sigma.Sum where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding
  using (DependentEncoding)
open import Prover.Category.Dependent.Sigma.Sum
  using (dependent-category-sigma-sum)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Encoding.Sigma.Sum
  using (encoding-sigma-sum)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## Types

dependent-encoding-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → (F₁ : DependentSplitFunctor C₁₁' C₂₁')
  → {A₁₁ A₂₁ A₂₂ : Set}
  → DependentEncoding C₁₁' A₁₁
  → DependentEncoding C₂₁' A₂₁
  → DependentEncoding C₂₂' A₂₂
  → DependentEncoding
    (dependent-category-sigma-sum C₂₂' F₁)
    (A₁₁ ⊔ A₂₁ × A₂₂)

-- ## Definitions

dependent-encoding-sigma-sum {n = zero} {C₂₂' = C₂₂'} _ e₁₁ e₂₁ e₂₂
  = encoding-sigma-sum
    (λ x₂₁ → Category.Object (DependentCategory.category C₂₂' x₂₁)) e₁₁ e₂₁
    (DependentEncoding.encoding e₂₂)

dependent-encoding-sigma-sum {n = suc _} F₁ e₁₁ e₂₁ e₂₂
  = record
  { encoding
    = λ x → dependent-encoding-sigma-sum
      (DependentSplitFunctor.split-functor F₁ x)
      (DependentEncoding.encoding e₁₁ x)
      (DependentEncoding.encoding e₂₁ x)
      (DependentEncoding.encoding e₂₂ x)
  }

