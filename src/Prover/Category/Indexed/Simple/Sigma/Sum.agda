module Prover.Category.Indexed.Simple.Sigma.Sum where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀)
open import Prover.Category.Indexed.Sigma.Sum
  using (indexed-category-sigma-sum)
open import Prover.Category.Indexed.Simple
  using (IndexedDependentSet; IndexedPartialFunction; IndexedSet; empty;
    indexed-partial-function₀; indexed-set₀; sigma)
open import Prover.Category.Indexed.Simple.Convert
  using (indexed-category-simple)
open import Prover.Category.Indexed.Simple.Sigma
  using (indexed-set-sigma)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor)
open import Prover.Category.Indexed.Unit
  using (indexed-category-unit)
open import Prover.Category.Simple.Sigma.Sum
  using (partial-function-sigma-sum)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## IndexedSet

indexed-set-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' D₁' : IndexedCategory C}
  → IndexedSet (chain-category-snoc D₁')
  → IndexedSplitFunctor C₁' D₁'
  → IndexedSet C
indexed-set-sigma-sum C₂' F₁
  = indexed-category-simple
  $ indexed-category-sigma-sum
    (indexed-category-unit C₂') F₁

-- ## IndexedPartialFunction

indexed-partial-function-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' D₁' : IndexedCategory C}
  → {C₂' D₂' : IndexedSet (chain-category-snoc D₁')}
  → (F₁ : IndexedSplitFunctor C₁' D₁')
  → IndexedPartialFunction C₂' D₂'
  → IndexedPartialFunction
    (indexed-set-sigma-sum C₂' F₁)
    (indexed-set-sigma D₁' D₂')
indexed-partial-function-sigma-sum
  {n = zero} {C₁' = C₁'} {D₁' = D₁'} {C₂' = C₂'} {D₂' = D₂'} F₁ F₂
  = empty
    (partial-function-sigma-sum
      (Category.Object
        (indexed-category₀ C₁'))
      (Category.Object
        (indexed-category₀ D₁'))
      (λ y₁ → indexed-set₀
        (IndexedSet.tail C₂' y₁))
      (λ y₁ → indexed-set₀
        (IndexedSet.tail D₂' y₁))
      (λ y₁ → indexed-partial-function₀
        (IndexedPartialFunction.tail F₂ y₁)))
indexed-partial-function-sigma-sum
  {n = suc _} F₁ F₂
  = sigma
    (λ x → indexed-partial-function-sigma-sum
      (IndexedSplitFunctor.tail F₁ x)
      (IndexedPartialFunction.tail F₂ x))

