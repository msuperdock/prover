module Prover.Function.Dependent.Split.Sigma.Maybe where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory; dependent-category₀)
open import Prover.Category.Dependent.Sigma.Maybe
  using (dependent-category-sigma-maybe)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction; cons; dependent-split-function₀; nil)
open import Prover.Function.Split.Sigma
  using (split-function-sigma)
open import Prover.Prelude

-- ## DependentSplitFunction

dependent-split-function-sigma-maybe
  : {A₁ A₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → DependentSplitFunction A₁ C₁'
  → DependentSplitFunction A₂ C₂'
  → DependentSplitFunction
    (A₁ × A₂)
    (dependent-category-sigma-maybe C₁' C₂')
dependent-split-function-sigma-maybe
  {n = zero} {C₂' = C₂'} F₁ F₂
  = nil
    (split-function-sigma
      (λ x₁ → Category.Object (dependent-category₀
        (DependentCategory.tail C₂' x₁)))
      (dependent-split-function₀ F₁)
      (λ x₁ → dependent-split-function₀
        (DependentSplitFunction.tail F₂ x₁)))
dependent-split-function-sigma-maybe
  {n = suc _} F₁ F₂
  = cons
    (λ x → dependent-split-function-sigma-maybe
      (DependentSplitFunction.tail F₁ x)
      (DependentSplitFunction.tail F₂ x))

